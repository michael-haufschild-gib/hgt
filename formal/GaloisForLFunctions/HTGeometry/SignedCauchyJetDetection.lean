import GaloisForLFunctions.HTGeometry.MeasureCauchyJetControllability

/-!
# Signed Cauchy-jet detection from the real part alone

A real-linear functional on a complex jet space only sees the real part of the pairing.  Detecting
coefficients from a real-linear annihilation therefore needs a detector that works from

```text
Re (Q t) = 0   almost everywhere
```

rather than from `Q t = 0`.

On the real axis `Re Q` is itself a Cauchy-jet form, carried by the *conjugate-doubled* node
family: conjugation sends a node in the upper half-plane to one in the lower half-plane, and
`conj ((t - x)⁻¹) = (t - conj x)⁻¹` for real `t`.  The two halves never collide, so the doubled
family is injective and consists of nodes off the real axis.  The signed detector applies and
returns the halved coefficients, hence the original ones.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex

noncomputable section

/-- Conjugating a Cauchy-jet form on the real axis conjugates both its nodes and coefficients. -/
theorem conj_cauchyJetForm {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ) (t : ℝ) :
    (starRingEnd ℂ) (cauchyJetForm x n c t) =
      cauchyJetForm (fun i => (starRingEnd ℂ) (x i)) n
        (fun i j => (starRingEnd ℂ) (c i j)) t := by
  rw [cauchyJetForm, cauchyJetForm, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [map_mul, map_pow, map_inv₀, map_sub, Complex.conj_ofReal]

/-- The conjugate-doubled node family of an upper-half-plane node family. -/
def doubledNodes {ι : Type*} (x : ι → ℂ) : ι ⊕ ι → ℂ :=
  Sum.elim x (fun i => (starRingEnd ℂ) (x i))

/-- The doubled coefficient packet carrying the real part. -/
def doubledCoefficients {ι : Type*} {n : ι → ℕ}
    (c : (i : ι) → Fin (n i) → ℂ) :
    (k : ι ⊕ ι) → Fin (Sum.elim n n k) → ℂ
  | Sum.inl i => fun j => c i j / 2
  | Sum.inr i => fun j => (starRingEnd ℂ) (c i j) / 2

theorem doubledNodes_im_ne_zero {ι : Type*} (x : ι → ℂ)
    (hupper : ∀ i, 0 < (x i).im) (k : ι ⊕ ι) : (doubledNodes x k).im ≠ 0 := by
  rcases k with i | i
  · exact ne_of_gt (hupper i)
  · have : ((starRingEnd ℂ) (x i)).im = -(x i).im := by simp
    rw [doubledNodes, Sum.elim_inr, this]
    exact neg_ne_zero.mpr (ne_of_gt (hupper i))

theorem doubledNodes_injective {ι : Type*} (x : ι → ℂ)
    (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im) :
    Function.Injective (doubledNodes x) := by
  have hconj : ∀ i, ((starRingEnd ℂ) (x i)).im = -(x i).im := by
    intro i; simp
  rintro (i | i) (k | k) h <;>
    simp only [doubledNodes, Sum.elim_inl, Sum.elim_inr] at h
  · exact congrArg Sum.inl (hx h)
  · exfalso
    have him := congrArg Complex.im h
    rw [hconj] at him
    have h1 := hupper i
    have h2 := hupper k
    linarith
  · exfalso
    have him := congrArg Complex.im h
    rw [hconj] at him
    have h1 := hupper i
    have h2 := hupper k
    linarith
  · refine congrArg Sum.inr (hx ?_)
    have := congrArg (starRingEnd ℂ) h
    simpa using this

/-- On the real axis the real part of a jet form is the jet form of the conjugate-doubled data. -/
theorem cauchyJetForm_doubled_eq_re {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ) (t : ℝ) :
    cauchyJetForm (doubledNodes x) (Sum.elim n n) (doubledCoefficients c) t =
      ((cauchyJetForm x n c t).re : ℂ) := by
  have hsplit :
      cauchyJetForm (doubledNodes x) (Sum.elim n n) (doubledCoefficients c) t =
        cauchyJetForm x n (fun i j => c i j / 2) t +
          cauchyJetForm (fun i => (starRingEnd ℂ) (x i)) n
            (fun i j => (starRingEnd ℂ) (c i j) / 2) t := by
    rw [cauchyJetForm, cauchyJetForm, cauchyJetForm, Fintype.sum_sum_type]
    rfl
  have hhalf : ∀ (y : ι → ℂ) (d : (i : ι) → Fin (n i) → ℂ),
      cauchyJetForm y n (fun i j => d i j / 2) t =
        cauchyJetForm y n d t / 2 := by
    intro y d
    rw [cauchyJetForm, cauchyJetForm, Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hsplit, hhalf, hhalf, ← conj_cauchyJetForm]
  have hac := Complex.add_conj (cauchyJetForm x n c t)
  push_cast at hac
  linear_combination hac / 2

/-- **Signed detection from the real part.**  If the real part of a finite Cauchy-jet form at
distinct upper-half-plane nodes vanishes almost everywhere against a measure of infinite support,
then every coefficient vanishes.  This is the form consumed by real-linear annihilation
arguments. -/
theorem cauchyJet_coeff_eq_zero_of_ae_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure ℝ} (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ)
    (hzero : ∀ᵐ t ∂μ, (cauchyJetForm x n c t).re = 0) :
    ∀ i j, c i j = 0 := by
  classical
  have hdoubled : ∀ (k : ι ⊕ ι) (j : Fin (Sum.elim n n k)),
      doubledCoefficients c k j = 0 := by
    apply cauchyJet_coeff_eq_zero_of_ae hsupp (doubledNodes x)
      (doubledNodes_injective x hx hupper)
      (doubledNodes_im_ne_zero x hupper) (Sum.elim n n)
    filter_upwards [hzero] with t ht
    have := cauchyJetForm_doubled_eq_re x n c t
    rw [cauchyJetForm] at this
    rw [this, ht]
    simp
  intro i j
  have h := hdoubled (Sum.inl i) j
  have h2 : c i j / 2 = 0 := h
  simpa using h2

/-- **Signed detection from real-part pairings.**  If every set integral of a finite Cauchy-jet
form has vanishing real part, then every coefficient vanishes.  This is the exact input produced by
a real-linear functional annihilating the range of a reweighting control map. -/
theorem cauchyJet_coeff_eq_zero_of_forall_setIntegral_re_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure ℝ} [IsFiniteMeasure μ] (hsupp : μ.support.Infinite)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (c : (i : ι) → Fin (n i) → ℂ)
    (hpair : ∀ S : Set ℝ, MeasurableSet S →
      (∫ t in S, cauchyJetForm x n c t ∂μ).re = 0) :
    ∀ i j, c i j = 0 := by
  have hne : ∀ i, (x i).im ≠ 0 := fun i => ne_of_gt (hupper i)
  have hint := integrable_cauchyJetForm μ x hne n c
  have hintre : Integrable (fun t => (cauchyJetForm x n c t).re) μ := hint.re
  have hzero : ∀ S : Set ℝ, MeasurableSet S → μ S < ⊤ →
      ∫ t in S, (cauchyJetForm x n c t).re ∂μ = 0 := by
    intro S hS _
    have hcomm : ∫ t in S, (cauchyJetForm x n c t).re ∂μ
        = (∫ t in S, cauchyJetForm x n c t ∂μ).re :=
      Complex.reCLM.integral_comp_comm hint.restrict
    rw [hcomm]
    exact hpair S hS
  have hae := Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero hintre hzero
  apply cauchyJet_coeff_eq_zero_of_ae_re hsupp x hx hupper n c
  filter_upwards [hae] with t ht
  exact ht

end

end GaloisForLFunctions.HTGeometry
