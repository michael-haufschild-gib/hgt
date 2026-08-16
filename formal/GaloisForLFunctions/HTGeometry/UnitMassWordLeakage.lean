import GaloisForLFunctions.HTGeometry.LocalPauliCapacityDegeneration
import GaloisForLFunctions.HTGeometry.IncidenceLeakageDimensionLoss

/-!
# Unit-mass syntheses and the leakage they carry

A synthesis of an operator as a combination of words with `ℓ¹` coefficient mass one is a convex
recipe, so Jensen's inequality bounds the leakage of the synthesized operator by the weighted mean
of the leakages of its words.  Summing that over a label set and dividing by the label count is the
incidence-normalized leakage estimate.

Unit mass is preserved by the bracket construction that generates high-weight labels from low ones:
if `a` and `b` are unit-mass words combinations and `‖ζ‖ = 2`, then `ζ⁻¹(ab - ba)` is again one,
because the bracket makes two copies and the scalar halves each.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

/-! ## Jensen for unit-mass combinations -/

/-- **A unit-mass combination has squared norm at most the weighted mean of squared norms.** -/
theorem norm_sum_sq_le_weighted {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (c : ι → ℂ) (x : ι → E) (hc : ∑ i, ‖c i‖ = 1) :
    ‖∑ i, c i • x i‖ ^ 2 ≤ ∑ i, ‖c i‖ * ‖x i‖ ^ 2 := by
  have htri : ‖∑ i, c i • x i‖ ≤ ∑ i, ‖c i‖ * ‖x i‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    exact Finset.sum_le_sum fun i _ => le_of_eq (norm_smul (c i) (x i))
  have hnn : (0 : ℝ) ≤ ∑ i, ‖c i‖ * ‖x i‖ :=
    Finset.sum_nonneg fun i _ => by positivity
  have hcs := sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt ‖c i‖)
    fun i => Real.sqrt ‖c i‖ * ‖x i‖
  have hprod : ∀ i : ι, Real.sqrt ‖c i‖ * (Real.sqrt ‖c i‖ * ‖x i‖) = ‖c i‖ * ‖x i‖ := by
    intro i
    rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  have hsqf : ∀ i : ι, Real.sqrt ‖c i‖ ^ 2 = ‖c i‖ := fun i => Real.sq_sqrt (norm_nonneg _)
  have hsqg : ∀ i : ι, (Real.sqrt ‖c i‖ * ‖x i‖) ^ 2 = ‖c i‖ * ‖x i‖ ^ 2 := by
    intro i
    rw [mul_pow, hsqf i]
  rw [Finset.sum_congr rfl fun i _ => hprod i, Finset.sum_congr rfl fun i _ => hsqf i,
    Finset.sum_congr rfl fun i _ => hsqg i, hc, one_mul] at hcs
  have hsq : ‖∑ i, c i • x i‖ ^ 2 ≤ (∑ i, ‖c i‖ * ‖x i‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖∑ i, c i • x i‖ := norm_nonneg _
    nlinarith [htri, h0, hnn]
  exact le_trans hsq hcs

/-! ## Jensen for Hilbert--Schmidt energy -/

variable {d : Type*} [Fintype d] [DecidableEq d]

omit [DecidableEq d] in
/-- **Unit-mass Jensen for Hilbert--Schmidt energy.** -/
theorem hsSqRe_sum_le_weighted {ι : Type*} [Fintype ι] (c : ι → ℂ) (W : ι → Matrix d d ℂ)
    (hc : ∑ i, ‖c i‖ = 1) :
    hsSqRe (∑ i, c i • W i) ≤ ∑ i, ‖c i‖ * hsSqRe (W i) := by
  have hentry : ∀ a b : d, (∑ i, c i • W i) b a = ∑ i, c i • W i b a := by
    intro a b
    simp [Matrix.sum_apply]
  have hstep : ∀ a b : d, ‖(∑ i, c i • W i) b a‖ ^ 2 ≤ ∑ i, ‖c i‖ * ‖W i b a‖ ^ 2 := by
    intro a b
    rw [hentry a b]
    exact norm_sum_sq_le_weighted (E := ℂ) c (fun i => W i b a) hc
  rw [hsSqRe_eq_sum]
  have hbound : ∑ a, ∑ b, ‖(∑ i, c i • W i) b a‖ ^ 2
      ≤ ∑ a, ∑ b, ∑ i, ‖c i‖ * ‖W i b a‖ ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hstep a b
  refine le_trans hbound (le_of_eq ?_)
  have hR : ∑ i, ‖c i‖ * hsSqRe (W i) = ∑ i, ∑ a, ∑ b, ‖c i‖ * ‖W i b a‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsSqRe_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
  rw [hR]
  calc ∑ a, ∑ b, ∑ i, ‖c i‖ * ‖W i b a‖ ^ 2
      = ∑ a, ∑ i, ∑ b, ‖c i‖ * ‖W i b a‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ‖c i‖ * ‖W i b a‖ ^ 2 := Finset.sum_comm

/-- **Unit-mass Jensen for cut leakage.**  The leakage of a synthesized operator is at most the
weighted mean of the leakages of its words. -/
theorem leak_sum_le_weighted {ι : Type*} [Fintype ι] (PU PV : Matrix d d ℂ) (c : ι → ℂ)
    (W : ι → Matrix d d ℂ) (hc : ∑ i, ‖c i‖ = 1) :
    hsSqRe ((1 - PV) * (∑ i, c i • W i) * PU)
      ≤ ∑ i, ‖c i‖ * hsSqRe ((1 - PV) * W i * PU) := by
  have hlin : (1 - PV) * (∑ i, c i • W i) * PU = ∑ i, c i • ((1 - PV) * W i * PU) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hlin]
  exact hsSqRe_sum_le_weighted c (fun i => (1 - PV) * W i * PU) hc

/-- **The incidence-normalized local-word leakage estimate.**  Any lower bound on the total label
leakage transfers, after normalization by the label count, to the word-level weighted sum. -/
theorem incidenceNormalized_leakage_ge {Q ι : Type*} [Fintype Q] [Fintype ι]
    (PU PV : Matrix d d ℂ) (c : Q → ι → ℂ) (W : Q → ι → Matrix d d ℂ)
    (hc : ∀ q, ∑ w, ‖c q w‖ = 1) {κ N : ℝ} (hN : 0 < N)
    (hlow : κ ≤ ∑ q, hsSqRe ((1 - PV) * (∑ w, c q w • W q w) * PU)) :
    κ / N ≤ (∑ q, ∑ w, ‖c q w‖ * hsSqRe ((1 - PV) * W q w * PU)) / N := by
  have hstep : κ ≤ ∑ q, ∑ w, ‖c q w‖ * hsSqRe ((1 - PV) * W q w * PU) := by
    refine le_trans hlow ?_
    exact Finset.sum_le_sum fun q _ => leak_sum_le_weighted PU PV (c q) (W q) (hc q)
  gcongr

/-! ## Unit mass survives the bracket -/

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- An element is a unit-mass synthesis over `S` when it is a finite combination of members of `S`
whose coefficients have `ℓ¹` mass one. -/
def HasUnitMassSynthesis (S : Set A) (a : A) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (w : ι → A),
    (∀ i, w i ∈ S) ∧ (∑ i, ‖c i‖) = 1 ∧ a = ∑ i, c i • w i

/-- A member of the word set is its own unit-mass synthesis. -/
theorem hasUnitMassSynthesis_of_mem {S : Set A} {a : A} (ha : a ∈ S) :
    HasUnitMassSynthesis S a := by
  refine ⟨Unit, inferInstance, fun _ => 1, fun _ => a, fun _ => ha, ?_, ?_⟩
  · simp
  · simp

/-- **Unit mass survives the halved bracket.**  If `a` and `b` are unit-mass syntheses over a
product-closed word set and `‖ζ‖ = 2`, then so is `ζ⁻¹(ab - ba)`: the bracket makes two copies and
the scalar halves each. -/
theorem hasUnitMassSynthesis_bracket {S : Set A} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)
    {a b : A} (ha : HasUnitMassSynthesis S a) (hb : HasUnitMassSynthesis S b)
    {ζ : ℂ} (hζ : ‖ζ‖ = 2) :
    HasUnitMassSynthesis S (ζ⁻¹ • (a * b - b * a)) := by
  obtain ⟨ι, hι, c, w, hw, hcm, hae⟩ := ha
  obtain ⟨κ, hκ, e, v, hv, hem, hbe⟩ := hb
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hζ
    norm_num at hζ
  classical
  refine ⟨(ι × κ) ⊕ (ι × κ), inferInstance,
    Sum.elim (fun p => ζ⁻¹ * c p.1 * e p.2) (fun p => -(ζ⁻¹ * c p.1 * e p.2)),
    Sum.elim (fun p => w p.1 * v p.2) (fun p => v p.2 * w p.1),
    ?_, ?_, ?_⟩
  · rintro (p | p)
    · exact hS _ (hw p.1) _ (hv p.2)
    · exact hS _ (hv p.2) _ (hw p.1)
  · have hhalf : ‖ζ⁻¹‖ = 1 / 2 := by
      rw [norm_inv, hζ]
      norm_num
    have hpiece : ∑ p : ι × κ, ‖ζ⁻¹ * c p.1 * e p.2‖ = 1 / 2 := by
      have hterm : ∀ p : ι × κ, ‖ζ⁻¹ * c p.1 * e p.2‖ = ‖ζ⁻¹‖ * (‖c p.1‖ * ‖e p.2‖) := by
        intro p
        rw [norm_mul, norm_mul, mul_assoc]
      rw [Finset.sum_congr rfl fun p _ => hterm p, ← Finset.mul_sum, Fintype.sum_prod_type]
      have hinner : ∀ i : ι, ∑ j : κ, ‖c i‖ * ‖e j‖ = ‖c i‖ := by
        intro i
        rw [← Finset.mul_sum, hem, mul_one]
      rw [Finset.sum_congr rfl fun i _ => hinner i, hcm, hhalf, mul_one]
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, norm_neg]
    rw [hpiece]
    norm_num
  · have hAB : ∑ p : ι × κ, (ζ⁻¹ * c p.1 * e p.2) • (w p.1 * v p.2) = ζ⁻¹ • (a * b) := by
      rw [hae, hbe, Finset.sum_mul_sum, Finset.smul_sum, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_smul, smul_smul, mul_assoc]
    have hBA : ∑ p : ι × κ, (ζ⁻¹ * c p.1 * e p.2) • (v p.2 * w p.1) = ζ⁻¹ • (b * a) := by
      rw [hae, hbe, Finset.sum_mul_sum, Finset.smul_sum, Fintype.sum_prod_type, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_smul, smul_smul]
      ring_nf
    have hneg : ∑ p : ι × κ, (-(ζ⁻¹ * c p.1 * e p.2)) • (v p.2 * w p.1) = -(ζ⁻¹ • (b * a)) := by
      rw [← hBA, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun p _ => neg_smul _ _
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hAB, hneg, smul_sub]
    abel

end GaloisForLFunctions.HTGeometry
