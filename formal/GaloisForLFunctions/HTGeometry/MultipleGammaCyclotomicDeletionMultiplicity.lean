import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaGenericSpectrum
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTransverseDADepth

/-!
# Multiple-Gamma deletion retains cyclotomic orbit multiplicity

On the dependent frame `(α, β, mα)` with `m ≥ 2` and `1, α, β` rationally independent, put
`F = Ψ₂(z; α, β, mα)` and `x_j = T_{τ_j} − 1`.  Because `τ₂ = m τ₀`, the translation group algebra
satisfies `g₂ = g₀^m`, so

```text
x₀ x₂ = (g₀ − 1)² (1 + g₀ + … + g₀^{m−1}) .
```

This file proves the analytic separation that makes the cyclotomic factor indispensable:

* `x₁ F` is differentially algebraic (deleting `β` leaves the rationally dependent pair `(α, mα)`);
* `x₀ x₂ F` is differentially algebraic (deleting both `α`-directions leaves the single period `β`);
* `x₀² F` is **hypertranscendental** — it is the order-one external defect
  `Δ_α Ψ₁(z; β, mα)`, and `α ∉ ℤ + ℤβ + ℤ(mα)` because `1 − nm ≠ 0` for `m ≥ 2`.

So the cyclotomic sum `1 + g₀ + … + g₀^{m−1}` carries an element out of the hypertranscendental
locus into the differentially algebraic one, and cannot be cancelled from the deletion ideal: the
radical, reduced zero set and minimum support depth of that ideal do not determine the analytic
translation-annihilator data.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-! ## The cyclotomic telescoping identity -/

/-- **Cyclotomic factorization of a structural multiple period.**
`Δ_{mα} = (∑_{i<m} T_{iα}) ∘ Δ_α`, the operator form of `g^m − 1 = (1+g+…+g^{m−1})(g−1)`. -/
theorem meroTranslationDefect_natCast_mul (m : ℕ) (α : ℂ) (y : meroField (Set.univ : Set ℂ)) :
    meroTranslationDefect ((m : ℂ) * α) y
      = ∑ i ∈ Finset.range m,
          addTranslationMeroEquiv ((i : ℂ) * α) (meroTranslationDefect α y) := by
  induction m with
  | zero => simp [meroTranslationDefect, addTranslationMeroEquiv_zero_apply]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hcast : ((n + 1 : ℕ) : ℂ) * α = (n : ℂ) * α + α := by push_cast; ring
    rw [hcast]
    simp only [meroTranslationDefect, map_sub, addTranslationMeroEquiv_add]
    ring

/-! ## The dependent frame -/

/-- The dependent period frame `(α, β, mα)`. -/
def cyclotomicFrame (m : ℕ) (α β : ℂ) : Fin 3 → ℂ := ![α, β, (m : ℂ) * α]

theorem cyclotomicFrame_im_pos {m : ℕ} (hm : 2 ≤ m) {α β : ℂ} (hα : 0 < α.im) (hβ : 0 < β.im) :
    ∀ i, 0 < (cyclotomicFrame m α β i).im := by
  intro i
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  fin_cases i
  · exact hα
  · exact hβ
  · show 0 < (((m : ℂ) * α).im)
    rw [Complex.mul_im]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    positivity

/-- The pair `(α, mα)` is rationally dependent together with `1`. -/
theorem not_linearIndependent_alpha_natMul {m : ℕ} (hm : 2 ≤ m) (α : ℂ) :
    ¬ LinearIndependent ℚ (ellipticGammaSourcePeriods α ((m : ℂ) * α)) := by
  intro hli
  have hzero : ∑ i : Fin 3, (![0, (m : ℚ), -1] : Fin 3 → ℚ) i •
      ellipticGammaSourcePeriods α ((m : ℂ) * α) i = 0 := by
    simp only [Fin.sum_univ_three, ellipticGammaSourcePeriods]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    simp only [Rat.smul_def]
    push_cast
    ring
  have hall := (Fintype.linearIndependent_iff.mp hli) _ hzero 1
  simp at hall
  omega

/-- The pair `(β, mα)` is rationally independent together with `1`. -/
theorem linearIndependent_beta_natMul {m : ℕ} (hm : 2 ≤ m) {α β : ℂ}
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods α β)) :
    LinearIndependent ℚ (ellipticGammaSourcePeriods β ((m : ℂ) * α)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hmne : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set g' : Fin 3 → ℚ := ![g 0, (m : ℚ) * g 2, g 1] with hg'
  have hzero : ∑ i : Fin 3, g' i • ellipticGammaSourcePeriods α β i = 0 := by
    have hg3 := hg
    simp only [Fin.sum_univ_three, ellipticGammaSourcePeriods] at hg3 ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at hg3 ⊢
    simp only [hg', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    simp only [Rat.smul_def] at hg3 ⊢
    push_cast at hg3 ⊢
    linear_combination hg3
  have hall := (Fintype.linearIndependent_iff.mp hind) g' hzero
  fin_cases i
  · simpa [hg'] using hall 0
  · simpa [hg'] using hall 2
  · have h2 := hall 1
    simp only [hg', Matrix.cons_val_one] at h2
    rcases mul_eq_zero.mp h2 with hcon | hres
    · exact absurd hcon hmne
    · simpa using hres

theorem not_linearIndependent_natMul_alpha {m : ℕ} (hm : 2 ≤ m) (α : ℂ) :
    ¬ LinearIndependent ℚ (ellipticGammaSourcePeriods ((m : ℂ) * α) α) := by
  intro hli
  have hzero : ∑ i : Fin 3, (![0, -1, (m : ℚ)] : Fin 3 → ℚ) i •
      ellipticGammaSourcePeriods ((m : ℂ) * α) α i = 0 := by
    simp only [Fin.sum_univ_three, ellipticGammaSourcePeriods]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    simp only [Rat.smul_def]
    push_cast
    ring
  have hall := (Fintype.linearIndependent_iff.mp hli) _ hzero 2
  simp at hall
  omega

/-! ## The three analytic statements on the dependent frame -/

variable {m : ℕ} {α β : ℂ}

/-- Deleting `β` leaves the rationally dependent pair `(α, mα)`: the face is differentially
algebraic. -/
theorem da_cyclotomicFrame_deleteBeta (hm : 2 ≤ m) (hα : 0 < α.im) (hβ : 0 < β.im) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
        (cyclotomicFrame_im_pos hm hα hβ) {1}) := by
  haveI : Nonempty (MultipleEllipticGammaFaceIndex ({1} : Finset (Fin 3))) :=
    ⟨⟨0, by decide⟩⟩
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_iff_not_rankThreeMinor]
  rintro ⟨q, r, hqr, hli⟩
  have hqv : ((q : Fin 3) : ℕ) = 0 ∨ ((q : Fin 3) : ℕ) = 2 := by
    have hq1 : (q : Fin 3) ≠ 1 := by simpa using q.2
    have hqlt : ((q : Fin 3) : ℕ) < 3 := (q : Fin 3).isLt
    have hqne : ((q : Fin 3) : ℕ) ≠ 1 := fun hc => hq1 (Fin.ext hc)
    omega
  have hrv : ((r : Fin 3) : ℕ) = 0 ∨ ((r : Fin 3) : ℕ) = 2 := by
    have hr1 : (r : Fin 3) ≠ 1 := by simpa using r.2
    have hrlt : ((r : Fin 3) : ℕ) < 3 := (r : Fin 3).isLt
    have hrne : ((r : Fin 3) : ℕ) ≠ 1 := fun hc => hr1 (Fin.ext hc)
    omega
  have hval0 : multipleEllipticGammaFaceParameters (cyclotomicFrame m α β) {1} q
      = cyclotomicFrame m α β (q : Fin 3) := rfl
  have hval1 : multipleEllipticGammaFaceParameters (cyclotomicFrame m α β) {1} r
      = cyclotomicFrame m α β (r : Fin 3) := rfl
  rw [hval0, hval1] at hli
  rcases hqv with hq | hq <;> rcases hrv with hr | hr
  · exact hqr (Subtype.ext (Fin.ext (by omega)))
  · rw [show (q : Fin 3) = 0 from Fin.ext hq, show (r : Fin 3) = 2 from Fin.ext hr] at hli
    exact not_linearIndependent_alpha_natMul hm α hli
  · rw [show (q : Fin 3) = 2 from Fin.ext hq, show (r : Fin 3) = 0 from Fin.ext hr] at hli
    exact not_linearIndependent_natMul_alpha hm α hli
  · exact hqr (Subtype.ext (Fin.ext (by omega)))

/-- Deleting both `α`-directions leaves the single period `β`: the face is differentially
algebraic. -/
theorem da_cyclotomicFrame_deleteAlphaPair (hm : 2 ≤ m) (hα : 0 < α.im) (hβ : 0 < β.im) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
        (cyclotomicFrame_im_pos hm hα hβ) {0, 2}) := by
  haveI : Nonempty (MultipleEllipticGammaFaceIndex ({0, 2} : Finset (Fin 3))) :=
    ⟨⟨1, by decide⟩⟩
  rw [differentialAlgebraicOver_multipleEllipticGammaLogDerivFaceMero_iff_not_rankThreeMinor]
  rintro ⟨q, r, hqr, -⟩
  have hq1 : (q : Fin 3) = 1 := by
    have hqm := q.2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hqm
    have hqlt : ((q : Fin 3) : ℕ) < 3 := (q : Fin 3).isLt
    have h0 : ((q : Fin 3) : ℕ) ≠ 0 := fun hc => hqm.1 (Fin.ext hc)
    have h2 : ((q : Fin 3) : ℕ) ≠ 2 := fun hc => hqm.2 (Fin.ext hc)
    exact Fin.ext (by omega)
  have hr1 : (r : Fin 3) = 1 := by
    have hrm := r.2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrm
    have hrlt : ((r : Fin 3) : ℕ) < 3 := (r : Fin 3).isLt
    have h0 : ((r : Fin 3) : ℕ) ≠ 0 := fun hc => hrm.1 (Fin.ext hc)
    have h2 : ((r : Fin 3) : ℕ) ≠ 2 := fun hc => hrm.2 (Fin.ext hc)
    exact Fin.ext (by omega)
  exact hqr (Subtype.ext (hq1.trans hr1.symm))

/-- The two labels surviving the deletion of `α`. -/
def cyclotomicFaceZeroEquiv :
    Fin 2 ≃ {i : Fin 3 // i ∉ ({0} : Finset (Fin 3))} :=
  Equiv.ofBijective
    (fun k => (![⟨1, by decide⟩, ⟨2, by decide⟩] :
      Fin 2 → {i : Fin 3 // i ∉ ({0} : Finset (Fin 3))}) k) (by decide)

theorem cyclotomicFrame_faceZero_eq (m : ℕ) (α β : ℂ) :
    (fun k : Fin 2 =>
        multipleEllipticGammaFaceParameters (cyclotomicFrame m α β) {0}
          (cyclotomicFaceZeroEquiv k))
      = ![β, (m : ℂ) * α] := by
  funext k
  fin_cases k <;> rfl

/-- **The doubled `α`-defect is hypertranscendental.**  It is the order-one external defect
`Δ_α Ψ₁(z; β, mα)`, and `α` is not in the rank-three period group `ℤ + ℤβ + ℤ(mα)` because
`1 − bm ≠ 0` for `m ≥ 2`. -/
theorem hypertranscendentalOver_cyclotomicFrame_alphaSquare (hm : 2 ≤ m)
    (hα : 0 < α.im) (hβ : 0 < β.im)
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods α β)) :
    HypertranscendentalOver (RatFunc ℂ)
      (meroTranslationDefect α
        (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
          (cyclotomicFrame_im_pos hm hα hβ) {0})) := by
  intro hDA
  have hpos := cyclotomicFrame_im_pos hm hα hβ
  have hβpos : 0 < β.im := hβ
  have hmαpos : 0 < ((m : ℂ) * α).im := hpos 2
  have hface : multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β) hpos {0}
      = multipleEllipticGammaLogDerivMero ![β, (m : ℂ) * α]
        (by
          intro i
          fin_cases i
          · exact hβpos
          · exact hmαpos) := by
    have hdef : multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β) hpos {0}
        = multipleEllipticGammaLogDerivMero
            (multipleEllipticGammaFaceParameters (cyclotomicFrame m α β) {0})
            (fun i => hpos i) := rfl
    rw [hdef]
    have hre := multipleEllipticGammaLogDerivMero_reindex cyclotomicFaceZeroEquiv
      (multipleEllipticGammaFaceParameters (cyclotomicFrame m α β) ({0} : Finset (Fin 3)))
      (fun i => hpos i)
    rw [← hre]
    congr 1
    exact cyclotomicFrame_faceZero_eq m α β
  rw [hface] at hDA
  obtain ⟨a, b, n, hval⟩ := exists_int_of_da_defect_fin_two β ((m : ℂ) * α) hβpos hmαpos
    (linearIndependent_beta_natMul hm hind) _ hDA
  -- a rational relation among 1, α, β with α-coefficient `b m − 1`
  have hzero : ∑ i : Fin 3, (![(a : ℚ), ((b : ℚ) * (m : ℚ) - 1), (n : ℚ)] : Fin 3 → ℚ) i •
      ellipticGammaSourcePeriods α β i = 0 := by
    simp only [Fin.sum_univ_three, ellipticGammaSourcePeriods]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    simp only [Rat.smul_def]
    push_cast
    linear_combination -hval
  have hall := (Fintype.linearIndependent_iff.mp hind) _ hzero 1
  simp at hall
  have hbm : (b : ℚ) * (m : ℚ) = 1 := by linarith [hall]
  have hbmZ : b * (m : ℤ) = 1 := by exact_mod_cast hbm
  have hm1 : (m : ℤ) ∣ 1 := ⟨b, by linarith [hbmZ]⟩
  have : (m : ℤ) ≤ 1 := Int.le_of_dvd one_pos hm1
  have hm2 : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  omega

/-! ## The deletion ideal on the dependent frame -/

theorem meroTranslationDefect_sum {κ : Type*} (h : ℂ) (s : Finset κ)
    (f : κ → meroField (Set.univ : Set ℂ)) :
    meroTranslationDefect h (∑ i ∈ s, f i) = ∑ i ∈ s, meroTranslationDefect h (f i) := by
  simp only [meroTranslationDefect, map_sum]
  rw [Finset.sum_sub_distrib]

/-- **The whole cyclotomic separation on the dependent frame `(α, β, mα)`.**

* `x₁ F` is differentially algebraic;
* `x₀ x₂ F` is differentially algebraic;
* `x₀² F` is hypertranscendental;
* `x₀ x₂ F = (1 + g₀ + … + g₀^{m−1}) · x₀² F`.

So the cyclotomic factor carries a hypertranscendental element into the differentially algebraic
locus and is analytically indispensable: it cannot be cancelled from the deletion ideal
`D = (x₁, x₀x₂)`. -/
theorem cyclotomicDeletionMultiplicity (hm : 2 ≤ m) (hα : 0 < α.im) (hβ : 0 < β.im)
    (hind : LinearIndependent ℚ (ellipticGammaSourcePeriods α β)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (meroTranslationDefect β
          (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
            (cyclotomicFrame_im_pos hm hα hβ) ∅))
      ∧ DifferentialAlgebraicOver (RatFunc ℂ)
        (meroTranslationDefect α (meroTranslationDefect ((m : ℂ) * α)
          (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
            (cyclotomicFrame_im_pos hm hα hβ) ∅)))
      ∧ HypertranscendentalOver (RatFunc ℂ)
        (meroTranslationDefect α (meroTranslationDefect α
          (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
            (cyclotomicFrame_im_pos hm hα hβ) ∅)))
      ∧ meroTranslationDefect α (meroTranslationDefect ((m : ℂ) * α)
          (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
            (cyclotomicFrame_im_pos hm hα hβ) ∅))
        = ∑ i ∈ Finset.range m, addTranslationMeroEquiv ((i : ℂ) * α)
            (meroTranslationDefect α (meroTranslationDefect α
              (multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β)
                (cyclotomicFrame_im_pos hm hα hβ) ∅))) := by
  set hpos := cyclotomicFrame_im_pos hm hα hβ with hposdef
  set F := multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β) hpos ∅ with hF
  have hτ0 : cyclotomicFrame m α β 0 = α := rfl
  have hτ1 : cyclotomicFrame m α β 1 = β := rfl
  have hτ2 : cyclotomicFrame m α β 2 = (m : ℂ) * α := rfl
  have hstep1 : meroTranslationDefect β F
      = multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β) hpos {1} := by
    have h := meroTranslationDefect_face (cyclotomicFrame m α β) hpos ∅ (q := 1) (by simp) (0 : ℂ)
    have h2 := multipleEllipticGammaLogDerivFaceMero_addTranslation_sub
      (cyclotomicFrame m α β) hpos ∅ 1 (by simp)
    rw [hτ1] at h2
    rw [show insert (1 : Fin 3) (∅ : Finset (Fin 3)) = ({1} : Finset (Fin 3)) by simp] at h2
    exact h2
  have hstep2 : meroTranslationDefect ((m : ℂ) * α) F
      = multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β) hpos {2} := by
    have h2 := multipleEllipticGammaLogDerivFaceMero_addTranslation_sub
      (cyclotomicFrame m α β) hpos ∅ 2 (by simp)
    rw [hτ2] at h2
    rw [show insert (2 : Fin 3) (∅ : Finset (Fin 3)) = ({2} : Finset (Fin 3)) by simp] at h2
    exact h2
  have hstep0 : meroTranslationDefect α F
      = multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β) hpos {0} := by
    have h2 := multipleEllipticGammaLogDerivFaceMero_addTranslation_sub
      (cyclotomicFrame m α β) hpos ∅ 0 (by simp)
    rw [hτ0] at h2
    rw [show insert (0 : Fin 3) (∅ : Finset (Fin 3)) = ({0} : Finset (Fin 3)) by simp] at h2
    exact h2
  have hstep02 : meroTranslationDefect α (meroTranslationDefect ((m : ℂ) * α) F)
      = multipleEllipticGammaLogDerivFaceMero (cyclotomicFrame m α β) hpos {0, 2} := by
    rw [hstep2]
    have h2 := multipleEllipticGammaLogDerivFaceMero_addTranslation_sub
      (cyclotomicFrame m α β) hpos {2} 0 (by decide)
    rw [hτ0] at h2
    exact h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hstep1]
    exact da_cyclotomicFrame_deleteBeta hm hα hβ
  · rw [hstep02]
    exact da_cyclotomicFrame_deleteAlphaPair hm hα hβ
  · rw [hstep0]
    exact hypertranscendentalOver_cyclotomicFrame_alphaSquare hm hα hβ hind
  · rw [meroTranslationDefect_natCast_mul m α F, meroTranslationDefect_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [meroTranslationDefect_addTranslation]

end

end GaloisForLFunctions
