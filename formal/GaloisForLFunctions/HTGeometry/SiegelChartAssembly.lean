import GaloisForLFunctions.HTGeometry.SiegelCoeffMap
import GaloisForLFunctions.HTGeometry.SiegelClearedCombination
import GaloisForLFunctions.HTGeometry.SiegelGainVanishing
import GaloisForLFunctions.HTGeometry.PolydiscCoeffVanishing

/-!
# The chartwise Siegel assembly

Putting the pieces together.  On each chart the estimated object is the denominator-cleared
combination of a *single* coefficient vector, so the Taylor conditions across all charts still
assemble into one linear map on the coefficient space, and the counting step still applies.  The
multi-index Schwarz estimate then gives, chart by chart, a gain relative to the bound on the large
tori.

Feeding that gain and a chart comparison constant into the chartwise closing mechanism makes every
cleared combination vanish on its small polydisc; where the denominators do not vanish this is a
genuine polynomial relation among the quotients, with nonzero coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n m : ℕ} {ι : Type*} [Fintype ι]

/-- The chartwise Taylor-condition map. -/
noncomputable def siegelHomCoeffMap (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hA : ∀ i k, Continuous (A i k)) (hB : ∀ i k, Continuous (B i k))
    (c : ι → (Fin n → ℂ)) {R : ℝ} (hR : 0 < R) (S : Finset (Fin n → ℕ)) :
    ((Fin (n + 1) → Fin (m + 1)) → ℂ) →ₗ[ℂ] ((ι × S) → ℂ) where
  toFun a := fun p =>
    polydiscCoeff (siegelHomCombination (A p.1) (B p.1) m a) (c p.1) R (p.2 : Fin n → ℕ)
  map_add' a b := by
    funext p
    rw [siegelHomCombination_add,
      polydiscCoeff_add hR (continuous_siegelHomCombination (hA p.1) (hB p.1) a)
        (continuous_siegelHomCombination (hA p.1) (hB p.1) b)]
    rfl
  map_smul' t a := by
    funext p
    rw [siegelHomCombination_smul, polydiscCoeff_const_smul]
    rfl

/-- **The chartwise Siegel gain.**  A single nonzero coefficient vector whose cleared combination
gains the Schwarz factor on every chart. -/
theorem exists_ne_zero_chart_siegel_gain {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hA : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (A i k)) (hB : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (B i k))
    (c : ι → (Fin n → ℂ)) {R r : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1)) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ M : ℝ, (∀ (i : ι) (t : Fin n → ℝ),
          ‖siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)‖ ≤ M) →
        ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
          ‖siegelHomCombination (A i) (B i) m a (c i + y)‖
            ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
              ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j := by
  classical
  have hAc : ∀ i k, Continuous (A i k) := fun i k => (hA i k).continuous
  have hBc : ∀ i k, Continuous (B i k) := fun i k => (hB i k).continuous
  obtain ⟨a, ha, hT⟩ :=
    exists_ne_zero_of_siegel_count (n := n) (m := m) (N := N) (lowDegreeIndices n N)
      (fun β hβ => mem_lowDegreeIndices.mp hβ)
      (siegelHomCoeffMap (m := m) A B hAc hBc c hR (lowDegreeIndices n N)) hcount
  refine ⟨a, ha, ?_⟩
  intro M hM i y hy
  refine norm_le_of_polydiscCoeff_vanish
    (differentiable_siegelHomCombination (hA i) (hB i) a) (c i) hR hr hrR (hM i) ?_ hy
  intro β hβ
  have := congrFun hT (i, ⟨β, mem_lowDegreeIndices.mpr hβ⟩)
  simpa [siegelHomCoeffMap] using this

/-- **The chartwise assembly.**  A gain beating the chart comparison makes a nonzero cleared
combination vanish on every small polydisc. -/
theorem exists_ne_zero_chart_vanishing [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hA : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (A i k)) (hB : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (B i k))
    (c : ι → (Fin n → ℂ)) {R r C : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (hcomp : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (M : ℝ),
      (∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
          ‖siegelHomCombination (A i) (B i) m a (c i + y)‖ ≤ M) →
      ∀ (i : ι) (t : Fin n → ℝ),
        ‖siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)‖ ≤ C * M)
    (hlt : C * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) < 1) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
        siegelHomCombination (A i) (B i) m a (c i + y) = 0 := by
  obtain ⟨a, ha, hgain⟩ :=
    exists_ne_zero_chart_siegel_gain (N := N) A B hA hB c hR hr hrR hcount
  refine ⟨a, ha, ?_⟩
  refine eqOn_zero_of_family_siegel_gain c (fun i => siegelHomCombination (A i) (B i) m a)
    (fun i => ((continuous_siegelHomCombination (fun k => (hA i k).continuous)
      (fun k => (hB i k).continuous) a).comp
        (continuous_const.add continuous_id)).continuousOn) hr ?_ (hcomp a) hlt
  intro M hM i y hy
  have := hgain M hM i y hy
  calc ‖siegelHomCombination (A i) (B i) m a (c i + y)‖
      ≤ M * (((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j := this
    _ = M * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) := by ring

omit [Fintype ι] in
/-- **The chart comparison from a transition structure.**  If every point of a large torus is, up to
a bounded factor, the value of some chart at a point of its small polydisc, the comparison constant
is that bound.  This is precisely what periodicity supplies for a chartwise Siegel argument: the
translate lands in the fundamental set, and the transition factor is the ratio of the two chart
denominators raised to the degree. -/
theorem hcomp_of_transition (F : ι → (Fin n → ℂ) → ℂ) (c : ι → (Fin n → ℂ))
    {r R C : ℝ} (hC : 0 ≤ C)
    (htrans : ∀ (i : ι) (t : Fin n → ℝ), ∃ (j : ι) (y : Fin n → ℂ) (u : ℂ),
      ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧ F i (torusMap (c i) (fun _ => R) t) = u * F j (c j + y)) :
    ∀ M : ℝ, (∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r → ‖F i (c i + y)‖ ≤ M) →
      ∀ (i : ι) (t : Fin n → ℝ), ‖F i (torusMap (c i) (fun _ => R) t)‖ ≤ C * M := by
  intro M hM i t
  obtain ⟨j, y, u, hy, hu, heq⟩ := htrans i t
  rw [heq, norm_mul]
  exact mul_le_mul hu (hM j y hy) (norm_nonneg _) hC

/-- **The chartwise assembly, with the geometric input in transition form.** -/
theorem exists_ne_zero_chart_vanishing_of_transition [Nonempty ι] {N : ℕ}
    (A B : ι → Fin (n + 1) → (Fin n → ℂ) → ℂ)
    (hA : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (A i k)) (hB : ∀ i k, ContDiff ℂ (⊤ : ℕ∞) (B i k))
    (c : ι → (Fin n → ℂ)) {R r C : ℝ} (hR : 0 < R) (hr : 0 ≤ r) (hrR : r < R) (hC : 0 ≤ C)
    (hcount : Fintype.card ι * N ^ n < (m + 1) ^ (n + 1))
    (htrans : ∀ (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (i : ι) (t : Fin n → ℝ),
      ∃ (j : ι) (y : Fin n → ℂ) (u : ℂ), ‖y‖ ≤ r ∧ ‖u‖ ≤ C ∧
        siegelHomCombination (A i) (B i) m a (torusMap (c i) (fun _ => R) t)
          = u * siegelHomCombination (A j) (B j) m a (c j + y))
    (hlt : C * ((((N + 1) ^ n : ℕ) : ℝ) * (r / R) ^ N *
        ∑' j : ℕ, (((j + 1) ^ n : ℕ) : ℝ) * (r / R) ^ j) < 1) :
    ∃ a : (Fin (n + 1) → Fin (m + 1)) → ℂ, a ≠ 0 ∧
      ∀ (i : ι) (y : Fin n → ℂ), ‖y‖ ≤ r →
        siegelHomCombination (A i) (B i) m a (c i + y) = 0 :=
  exists_ne_zero_chart_vanishing (N := N) A B hA hB c hR hr hrR hcount
    (fun a => hcomp_of_transition (fun i => siegelHomCombination (A i) (B i) m a) c hC
      (htrans a)) hlt

end GaloisForLFunctions.HTGeometry
