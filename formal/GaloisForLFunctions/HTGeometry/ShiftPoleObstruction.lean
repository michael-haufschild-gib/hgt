import GaloisForLFunctions.HTGeometry.ShiftPolePartCalculus
import GaloisForLFunctions.HTGeometry.PrincipalPartDecomposition

/-!
# The obstruction functional of a first-order equation

The linear functional `Θ^λ_β(u) = ∑_{d ≥ 1} ((-λ)^{d-1}/(d-1)!) · polePart u β d` vanishes on the
image of `f ↦ f′ - λ f`, transforms under translation by moving the pole location, and has finite
support in `β`.  A shift-periodic finitely supported family vanishes, which is the orbit
obstruction of the one-shift equation.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

/-- The pole coefficients of a rational function are finitely supported. -/
theorem finite_support_polePart (u : RatFunc ℂ) :
    (Function.support fun p : ℂ × ℕ => polePart u p.1 (p.2 + 1)).Finite := by
  classical
  obtain ⟨R, c, hcpos, hc, hdec⟩ := exists_principalPart_decomposition u
  refine Set.Finite.subset (Set.Finite.image (fun q : ℂ × ℕ => (q.1, q.2 - 1))
    (Finset.finite_toSet c.support)) ?_
  intro p hp
  simp only [Function.mem_support, ne_eq] at hp
  refine ⟨(p.1, p.2 + 1), ?_, by simp⟩
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq]
  rw [hc p.1 (p.2 + 1) (by omega)]
  exact hp

theorem finite_support_polePart_at (u : RatFunc ℂ) (β : ℂ) :
    (Function.support fun d : ℕ => polePart u β (d + 1)).Finite := by
  classical
  have hinj : Function.Injective fun d : ℕ => (β, d) := by
    intro d e h
    simpa using h
  refine Set.Finite.of_finite_image (f := fun d : ℕ => (β, d)) ?_ (hinj.injOn)
  refine Set.Finite.subset (finite_support_polePart u) ?_
  rintro p ⟨d, hd, rfl⟩
  simpa using hd

/-- The truncated obstruction functional. -/
def ThetaN (lam : ℂ) (u : RatFunc ℂ) (β : ℂ) (N : ℕ) : ℂ :=
  ∑ d ∈ Finset.range N, ((-lam) ^ d / (Nat.factorial d : ℂ)) * polePart u β (d + 1)

/-- The obstruction functional of the operator `f ↦ f′ - λ f` at the pole `β`. -/
def Theta (lam : ℂ) (u : RatFunc ℂ) (β : ℂ) : ℂ :=
  ∑ᶠ d : ℕ, ((-lam) ^ d / (Nat.factorial d : ℂ)) * polePart u β (d + 1)

theorem Theta_eq_ThetaN (lam : ℂ) (u : RatFunc ℂ) (β : ℂ) {N : ℕ}
    (hN : ∀ d, N ≤ d → polePart u β (d + 1) = 0) :
    Theta lam u β = ThetaN lam u β N := by
  classical
  refine finsum_eq_sum_of_support_subset _ ?_
  intro d hd
  simp only [Function.mem_support, ne_eq] at hd
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra hcon
  exact hd (by rw [hN d (by omega), mul_zero])

theorem ThetaN_stable (lam : ℂ) (u : RatFunc ℂ) (β : ℂ) {N M : ℕ} (hNM : N ≤ M)
    (hN : ∀ d, N ≤ d → polePart u β (d + 1) = 0) :
    ThetaN lam u β M = ThetaN lam u β N := by
  classical
  rw [ThetaN, ThetaN, ← Finset.sum_range_add_sum_Ico _ hNM]
  have hzero : ∑ d ∈ Finset.Ico N M, ((-lam) ^ d / (Nat.factorial d : ℂ)) *
      polePart u β (d + 1) = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [hN d (Finset.mem_Ico.mp hd).1, mul_zero]
  rw [hzero, add_zero]

/-- The pole coefficients of the first-order image. -/
theorem polePart_deriv_sub (lam : ℂ) (v : RatFunc ℂ) (β : ℂ) (d : ℕ) :
    polePart (ratFuncDerivative ℂ v - algebraMap ℂ (RatFunc ℂ) lam * v) β (d + 1)
      = -(d : ℂ) * polePart v β d - lam * polePart v β (d + 1) := by
  rw [sub_eq_add_neg, polePart_add, polePart_neg, polePart_smul, polePart_ratFuncDerivative,
    sub_eq_add_neg]

/-- **The truncated obstruction of a first-order image is a boundary term.** -/
theorem ThetaN_deriv_sub_succ (lam : ℂ) (v : RatFunc ℂ) (β : ℂ) (N : ℕ) :
    ThetaN lam (ratFuncDerivative ℂ v - algebraMap ℂ (RatFunc ℂ) lam * v) β (N + 1)
      = -(lam * ((-lam) ^ N / (Nat.factorial N : ℂ))) * polePart v β (N + 1) := by
  induction N with
  | zero =>
      rw [ThetaN, Finset.sum_range_one, polePart_deriv_sub]
      norm_num
  | succ N ih =>
      rw [ThetaN, Finset.sum_range_succ, ← ThetaN, ih, polePart_deriv_sub]
      have hfac : ((Nat.factorial (N + 1) : ℂ)) = ((N : ℂ) + 1) * (Nat.factorial N : ℂ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have hfacne : ((Nat.factorial N : ℂ)) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]
        exact Nat.factorial_ne_zero N
      have hne : ((N : ℂ) + 1) ≠ 0 := by
        intro hc
        have : ((N : ℂ) + 1).re = 0 := by rw [hc]; simp
        simp at this
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      rw [hfac]
      field_simp
      push_cast
      ring

/-- **The obstruction vanishes on the image of the first-order operator.** -/
theorem Theta_deriv_sub (lam : ℂ) (v : RatFunc ℂ) (β : ℂ) :
    Theta lam (ratFuncDerivative ℂ v - algebraMap ℂ (RatFunc ℂ) lam * v) β = 0 := by
  classical
  set w : RatFunc ℂ := ratFuncDerivative ℂ v - algebraMap ℂ (RatFunc ℂ) lam * v with hw
  obtain ⟨s₁, hs₁⟩ := (finite_support_polePart_at w β).exists_finset
  obtain ⟨s₂, hs₂⟩ := (finite_support_polePart_at v β).exists_finset
  set M : ℕ := max (s₁.sup id) (s₂.sup id) + 1 with hM
  have hw0 : ∀ d, (M + 1) ≤ d → polePart w β (d + 1) = 0 := by
    intro d hd
    by_contra hc
    have hmem : d ∈ s₁ := (hs₁ d).mpr hc
    have hle : d ≤ s₁.sup id := Finset.le_sup (f := id) hmem
    have : s₁.sup id < M := by
      rw [hM]
      exact Nat.lt_succ_of_le (le_max_left _ _)
    omega
  have hv0 : polePart v β (M + 1) = 0 := by
    by_contra hc
    have hmem : M ∈ s₂ := (hs₂ M).mpr hc
    have hle : M ≤ s₂.sup id := Finset.le_sup (f := id) hmem
    have : s₂.sup id < M := by
      rw [hM]
      exact Nat.lt_succ_of_le (le_max_right _ _)
    omega
  rw [Theta_eq_ThetaN lam w β hw0, hw, ThetaN_deriv_sub_succ, hv0, mul_zero]

/-- **Translation moves the obstruction along the pole orbit.** -/
theorem Theta_ratFuncShift (lam a : ℂ) (u : RatFunc ℂ) (β : ℂ) :
    Theta lam (ratFuncShift a u) β = Theta lam u (β + a) := by
  rw [Theta, Theta]
  refine finsum_congr fun d => ?_
  rw [polePart_ratFuncShift]

theorem finite_support_Theta (lam : ℂ) (u : RatFunc ℂ) :
    (Function.support fun β : ℂ => Theta lam u β).Finite := by
  classical
  refine Set.Finite.subset (Set.Finite.image Prod.fst (finite_support_polePart u)) ?_
  intro β hβ
  simp only [Function.mem_support, ne_eq] at hβ
  have hex : ∃ d : ℕ, polePart u β (d + 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hβ ?_
    rw [Theta]
    refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [hcon d, mul_zero]
  obtain ⟨d, hd⟩ := hex
  exact ⟨(β, d), by simpa using hd, rfl⟩

/-- **A shift-periodic obstruction vanishes.** -/
theorem Theta_eq_zero_of_periodic {lam h : ℂ} (hh : h ≠ 0) {u : RatFunc ℂ}
    (hper : ∀ β : ℂ, Theta lam u (β + h) = Theta lam u β) (β : ℂ) :
    Theta lam u β = 0 := by
  classical
  by_contra hcon
  have hall : ∀ n : ℕ, Theta lam u (β + n * h) = Theta lam u β := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have : β + ((n : ℂ) + 1) * h = (β + n * h) + h := by ring
        rw [show ((n + 1 : ℕ) : ℂ) = (n : ℂ) + 1 by push_cast; ring, this, hper, ih]
  have hsub : Set.range (fun n : ℕ => β + n * h) ⊆ Function.support fun γ : ℂ => Theta lam u γ := by
    rintro γ ⟨n, rfl⟩
    simp only [Function.mem_support, ne_eq]
    rw [hall n]
    exact hcon
  have hinj : Function.Injective fun n : ℕ => β + (n : ℂ) * h := by
    intro m n hmn
    simp only at hmn
    have : (m : ℂ) * h = (n : ℂ) * h := by linear_combination hmn
    have hmn' : (m : ℂ) = (n : ℂ) := mul_right_cancel₀ hh this
    exact_mod_cast hmn'
  exact (Set.infinite_range_of_injective hinj) ((finite_support_Theta lam u).subset hsub)

end

end GaloisForLFunctions.HTGeometry
