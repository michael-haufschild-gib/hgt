import GaloisForLFunctions.HTGeometry.ExpJetSubstitution
import GaloisForLFunctions.HTGeometry.PeriodicAutonomousDescent

/-!
# Differential algebraicity descends through composition with an exponential

If `g` is entire and `g (exp (a z))` satisfies an algebraic differential equation, so does `g`.

The naive attempt fails because a relation for the composite may involve the point `z`, and `z` is
`log w / a`, which is not algebraic over `ℂ(w)`.  Periodicity removes that obstruction in advance:
`g (exp (a ·))` has period `2πi/a`, so the autonomy descent replaces the relation by one with no
point slot.  Substituting the exponential jet transfer into an autonomous relation is then a purely
polynomial operation, and the substitution is injective, so the transferred relation is nonzero.

* **`differentiallyAlgebraic_of_comp_exp`** — the descent;
* **`hypertranscendental_comp_exp`** — its contrapositive.
-/

open Finset MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- The transfer identity in the form the substitution consumes: a jet of the composite is the
transfer matrix applied to the weighted jets of `g`. -/
theorem iteratedDeriv_comp_exp_fin {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) (a : ℂ) (n : ℕ)
    (k : Fin (n + 1)) (z : ℂ) :
    iteratedDeriv (k : ℕ) (fun w => g (Complex.exp (a * w))) z
      = expJetLinear a n (fun j : Fin (n + 1) =>
          Complex.exp (a * z) ^ (j : ℕ) * iteratedDeriv (j : ℕ) g (Complex.exp (a * z))) k := by
  have hwiden : ∑ j ∈ range ((k : ℕ) + 1), expJetCoeff a (k : ℕ) j *
        Complex.exp (a * z) ^ j * iteratedDeriv j g (Complex.exp (a * z))
      = ∑ j ∈ range (n + 1), expJetCoeff a (k : ℕ) j *
        Complex.exp (a * z) ^ j * iteratedDeriv j g (Complex.exp (a * z)) := by
    have hk : (k : ℕ) ≤ n := Nat.lt_succ_iff.mp k.isLt
    refine sum_subset (fun x hx => ?_) ?_
    · rw [mem_range] at hx ⊢
      omega
    intro x _ hnx
    have hx : (k : ℕ) + 1 ≤ x := by simpa [mem_range, Nat.not_lt] using hnx
    rw [expJetCoeff_eq_zero_of_lt a (by omega), zero_mul, zero_mul]
  rw [iteratedDeriv_comp_exp hg a (k : ℕ) z, hwiden, expJetLinear_apply,
    Fin.sum_univ_eq_sum_range (fun j => expJetCoeff a (k : ℕ) j *
      (Complex.exp (a * z) ^ j * iteratedDeriv j g (Complex.exp (a * z)))) (n + 1)]
  exact sum_congr rfl fun j _ => by ring

/-- The monomial substitution restoring the point variable: `Yⱼ ↦ X₀ʲ · X_{j+1}`. -/
noncomputable def expWeightSubst (n : ℕ) : Fin (n + 1) → MvPolynomial (Fin (n + 2)) ℂ :=
  fun j => X 0 ^ (j : ℕ) * X j.succ

theorem eval_expWeightSubst (n : ℕ) (w : ℂ) (Y : Fin (n + 1) → ℂ) (j : Fin (n + 1)) :
    eval (Fin.cons w Y) (expWeightSubst n j) = w ^ (j : ℕ) * Y j := by
  simp [expWeightSubst]

/-- The monomial substitution preserves nonzeroness: evaluate at `w = 1`. -/
theorem bind₁_expWeightSubst_ne_zero {n : ℕ} {S : MvPolynomial (Fin (n + 1)) ℂ} (hS : S ≠ 0) :
    bind₁ (expWeightSubst n) S ≠ 0 := by
  intro h0
  apply hS
  refine MvPolynomial.funext fun Y => ?_
  have hev : eval₂Hom (RingHom.id ℂ) (Fin.cons 1 Y) (bind₁ (expWeightSubst n) S) = 0 := by
    rw [h0, map_zero]
  rw [eval₂Hom_bind₁] at hev
  have hpt : (fun j => eval₂Hom (RingHom.id ℂ) (Fin.cons 1 Y) (expWeightSubst n j)) = Y := by
    funext j
    rw [show eval₂Hom (RingHom.id ℂ) (Fin.cons (1 : ℂ) Y) (expWeightSubst n j)
      = eval (Fin.cons (1 : ℂ) Y) (expWeightSubst n j) from rfl, eval_expWeightSubst]
    simp
  rw [hpt] at hev
  rw [show eval Y S = eval₂Hom (RingHom.id ℂ) Y S from rfl, hev, map_zero]

/-! ### The descent -/

/-- **Differential algebraicity descends through an exponential.**  For entire `g` and `a ≠ 0`, if
`g (exp (a z))` is differentially algebraic then so is `g`. -/
theorem differentiallyAlgebraic_of_comp_exp {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) {a : ℂ}
    (ha : a ≠ 0) (hDA : DifferentiallyAlgebraic (fun z => g (Complex.exp (a * z)))) :
    DifferentiallyAlgebraic g := by
  classical
  set c : ℂ := 2 * Real.pi * Complex.I / a with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    refine div_ne_zero ?_ ha
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hper : Function.Periodic (fun z => g (Complex.exp (a * z))) c := by
    intro z
    have hac : a * (z + c) = a * z + 2 * Real.pi * Complex.I := by
      rw [hcdef]
      field_simp
    show g (Complex.exp (a * (z + c))) = g (Complex.exp (a * z))
    rw [hac, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  obtain ⟨n, R, hR, hRz⟩ := exists_autonomousJet_of_periodic hc0 hper hDA
  set S : MvPolynomial (Fin (n + 1)) ℂ := bind₁ (expJetSubst a n) R with hSdef
  have hS : S ≠ 0 := bind₁_expJetSubst_ne_zero ha hR
  set T : MvPolynomial (Fin (n + 2)) ℂ := bind₁ (expWeightSubst n) S with hTdef
  have hT : T ≠ 0 := bind₁_expWeightSubst_ne_zero hS
  have hTeval : ∀ w : ℂ, w ≠ 0 →
      eval (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g w)) T = 0 := by
    intro w hw
    obtain ⟨z, hz⟩ : ∃ z : ℂ, Complex.exp (a * z) = w := by
      refine ⟨Complex.log w / a, ?_⟩
      rw [mul_div_cancel₀ _ ha, Complex.exp_log hw]
    have hY : (fun j : Fin (n + 1) => eval
        (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g w)) (expWeightSubst n j))
        = fun j : Fin (n + 1) => Complex.exp (a * z) ^ (j : ℕ) *
            iteratedDeriv (j : ℕ) g (Complex.exp (a * z)) := by
      funext j
      rw [eval_expWeightSubst, hz]
    have e1 : eval (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g w)) T
        = eval (fun j : Fin (n + 1) =>
            eval (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g w))
              (expWeightSubst n j)) S := by
      rw [hTdef]
      exact eval₂Hom_bind₁ (RingHom.id ℂ) _ _ S
    have e2 : eval (fun j : Fin (n + 1) => Complex.exp (a * z) ^ (j : ℕ) *
            iteratedDeriv (j : ℕ) g (Complex.exp (a * z))) S
        = eval (fun k : Fin (n + 1) =>
            eval (fun j : Fin (n + 1) => Complex.exp (a * z) ^ (j : ℕ) *
              iteratedDeriv (j : ℕ) g (Complex.exp (a * z))) (expJetSubst a n k)) R := by
      rw [hSdef]
      exact eval₂Hom_bind₁ (RingHom.id ℂ) _ _ R
    have e3 : (fun k : Fin (n + 1) =>
          eval (fun j : Fin (n + 1) => Complex.exp (a * z) ^ (j : ℕ) *
            iteratedDeriv (j : ℕ) g (Complex.exp (a * z))) (expJetSubst a n k))
        = fun k : Fin (n + 1) =>
            iteratedDeriv (k : ℕ) (fun u => g (Complex.exp (a * u))) z := by
      funext k
      rw [eval_expJetSubst, ← iteratedDeriv_comp_exp_fin hg a n k z]
    have hstep : eval (Fin.cons w (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g w)) T
        = eval (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ)
            (fun u => g (Complex.exp (a * u))) z) R := by
      rw [e1, hY, e2, e3]
    rw [hstep, hRz z]
  refine ⟨n, X 0 * T, mul_ne_zero (X_ne_zero 0) hT, fun w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    simp
  · rw [map_mul, hTeval w hw, mul_zero]

/-- **Hypertranscendence is inherited by the exponential composite.** -/
theorem hypertranscendental_comp_exp {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g) {a : ℂ} (ha : a ≠ 0)
    (hHT : Hypertranscendental g) :
    Hypertranscendental (fun z => g (Complex.exp (a * z))) :=
  fun hDA => hHT (differentiallyAlgebraic_of_comp_exp hg ha hDA)


/-! ### The composite as a periodic function -/

/-- The exponential composite has period `2πi/a`. -/
theorem periodic_comp_exp (g : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) :
    Function.Periodic (fun z => g (Complex.exp (a * z))) (2 * Real.pi * Complex.I / a) := by
  intro z
  have hac : a * (z + 2 * Real.pi * Complex.I / a)
      = a * z + 2 * Real.pi * Complex.I := by field_simp
  show g (Complex.exp (a * (z + 2 * Real.pi * Complex.I / a)))
      = g (Complex.exp (a * z))
  rw [hac, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem twoPiI_div_ne_zero {a : ℂ} (ha : a ≠ 0) :
    (2 * Real.pi * Complex.I / a : ℂ) ≠ 0 := by
  refine div_ne_zero ?_ ha
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- **Every entire hypertranscendental function has a periodic hypertranscendental exponential
composite.**  This is the general construction behind the witness that inhabits the period
dichotomy. -/
theorem periodic_and_hypertranscendental_comp_exp {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g)
    (hHT : Hypertranscendental g) {a : ℂ} (ha : a ≠ 0) :
    Function.Periodic (fun z => g (Complex.exp (a * z))) (2 * Real.pi * Complex.I / a) ∧
      Hypertranscendental (fun z => g (Complex.exp (a * z))) :=
  ⟨periodic_comp_exp g ha, hypertranscendental_comp_exp hg ha hHT⟩

end GaloisForLFunctions.HTGeometry
