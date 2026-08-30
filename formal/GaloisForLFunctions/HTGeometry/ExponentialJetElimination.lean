import GaloisForLFunctions.HTGeometry.JetDifferentialRing
import GaloisForLFunctions.HTGeometry.PeriodicAutonomousDescent

/-!
# Eliminating an exponential from a differential relation

A differential relation obtained by transporting an equation along `z ↦ exp (a z)` is polynomial in
the jets of the transported function *and* in `exp (a z)` itself.  The exponential is not algebraic
over the point, so it cannot simply be discarded; it is removed instead by a degree induction.

Total differentiation acts on such a relation coefficientwise on the jets and multiplies the
coefficient of `Xᵈ` by `d·a`, so it preserves the degree in the exponential variable.  Combining a
relation with its total derivative and clearing the leading coefficient produces a relation of
strictly smaller exponential degree.  When that combination is identically zero the coefficients
satisfy `c_D·𝒟c_d − c_d·𝒟c_D = (D−d)·a·c_d·c_D`, which the jet ring forbids unless `c_d` vanishes;
the relation is then a single monomial, and the exponential — being nowhere zero — divides out.

* `GaloisForLFunctions.HTGeometry.expJetEvalHom`;
* `GaloisForLFunctions.HTGeometry.expJetTotalDeriv`;
* `GaloisForLFunctions.HTGeometry.exists_autonomousJet_of_expJetRelation`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial JetRing

noncomputable section

/-- Jet polynomials carrying one extra variable for an exponential. -/
abbrev ExpJetPoly := Polynomial (MvPolynomial ℕ ℂ)

/-- Realization of an exponential jet polynomial: the polynomial variable carries `exp (a z)` and
the jet variables carry the jets of `h` at `z`. -/
def expJetEvalHom (a : ℂ) (h : ℂ → ℂ) (z : ℂ) : ExpJetPoly →+* ℂ :=
  (Polynomial.evalRingHom (Complex.exp (a * z))).comp
    (Polynomial.mapRingHom (MvPolynomial.eval (jetVector h z)))

@[simp] theorem expJetEvalHom_C (a : ℂ) (h : ℂ → ℂ) (z : ℂ) (q : MvPolynomial ℕ ℂ) :
    expJetEvalHom a h z (Polynomial.C q) = MvPolynomial.eval (jetVector h z) q := by
  simp [expJetEvalHom]

@[simp] theorem expJetEvalHom_X (a : ℂ) (h : ℂ → ℂ) (z : ℂ) :
    expJetEvalHom a h z Polynomial.X = Complex.exp (a * z) := by
  simp [expJetEvalHom]

theorem expJetEvalHom_eq_sum_range (a : ℂ) (h : ℂ → ℂ) (z : ℂ) {F : ExpJetPoly} {M : ℕ}
    (hM : F.natDegree < M) :
    expJetEvalHom a h z F
      = ∑ d ∈ Finset.range M,
          MvPolynomial.eval (jetVector h z) (F.coeff d) * Complex.exp (a * z) ^ d := by
  have hdeg : (F.map (MvPolynomial.eval (jetVector h z))).natDegree < M :=
    lt_of_le_of_lt (Polynomial.natDegree_map_le) hM
  rw [expJetEvalHom]
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom,
    Polynomial.coe_evalRingHom]
  rw [Polynomial.eval_eq_sum_range' hdeg]
  exact Finset.sum_congr rfl fun d _ => by rw [Polynomial.coeff_map]

/-! ### The total derivative -/

/-- Coefficientwise jet differentiation. -/
def jetCoeffDeriv (F : ExpJetPoly) : ExpJetPoly :=
  ∑ d ∈ F.support, Polynomial.monomial d (jetDeriv (F.coeff d))

theorem coeff_jetCoeffDeriv (F : ExpJetPoly) (e : ℕ) :
    (jetCoeffDeriv F).coeff e = jetDeriv (F.coeff e) := by
  classical
  rw [jetCoeffDeriv, Polynomial.finsetSum_coeff]
  by_cases he : e ∈ F.support
  · rw [Finset.sum_eq_single e]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _ hbe
      rw [Polynomial.coeff_monomial, if_neg hbe]
    · intro hcon
      exact absurd he hcon
  · have h0 : F.coeff e = 0 := Polynomial.notMem_support_iff.1 he
    rw [h0, map_zero]
    refine Finset.sum_eq_zero fun d hd => ?_
    have hde : d ≠ e := fun hh => he (hh ▸ hd)
    rw [Polynomial.coeff_monomial, if_neg hde]

private theorem coeff_X_mul_derivative (F : ExpJetPoly) (e : ℕ) :
    (Polynomial.X * Polynomial.derivative F).coeff e
      = (e : MvPolynomial ℕ ℂ) * F.coeff e := by
  cases e with
  | zero => simp [Polynomial.mul_coeff_zero]
  | succ m =>
      rw [Polynomial.coeff_X_mul, Polynomial.coeff_derivative]
      push_cast
      ring

/-- Total differentiation of an exponential jet polynomial: jets advance and the exponential
variable contributes its logarithmic derivative. -/
def expJetTotalDeriv (a : ℂ) (F : ExpJetPoly) : ExpJetPoly :=
  jetCoeffDeriv F + Polynomial.C (MvPolynomial.C a) * (Polynomial.X * Polynomial.derivative F)

theorem coeff_expJetTotalDeriv (a : ℂ) (F : ExpJetPoly) (e : ℕ) :
    (expJetTotalDeriv a F).coeff e
      = jetDeriv (F.coeff e) + MvPolynomial.C (a * (e : ℂ)) * F.coeff e := by
  have hC : (MvPolynomial.C (a * (e : ℂ)) : MvPolynomial ℕ ℂ)
      = MvPolynomial.C a * (e : MvPolynomial ℕ ℂ) := by
    rw [map_mul]
    congr 1
  rw [expJetTotalDeriv, Polynomial.coeff_add, coeff_jetCoeffDeriv, Polynomial.coeff_C_mul,
    coeff_X_mul_derivative, hC, mul_assoc]

theorem natDegree_expJetTotalDeriv_le (a : ℂ) (F : ExpJetPoly) :
    (expJetTotalDeriv a F).natDegree ≤ F.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun e he => ?_
  have h0 : F.coeff e = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt he
  rw [coeff_expJetTotalDeriv, h0, map_zero, mul_zero, add_zero]

/-- Derivative of an exponential power. -/
theorem hasDerivAt_exp_pow (a : ℂ) (d : ℕ) (z : ℂ) :
    HasDerivAt (fun w => Complex.exp (a * w) ^ d)
      (a * (d : ℂ) * Complex.exp (a * z) ^ d) z := by
  have hpow : ∀ w : ℂ, Complex.exp (a * w) ^ d = Complex.exp (((d : ℂ) * a) * w) := by
    intro w
    rw [mul_assoc, Complex.exp_nat_mul]
  have hlin : HasDerivAt (fun w : ℂ => ((d : ℂ) * a) * w) ((d : ℂ) * a) z := by
    simpa using (hasDerivAt_id z).const_mul ((d : ℂ) * a)
  have hcomp : HasDerivAt (fun w : ℂ => Complex.exp (((d : ℂ) * a) * w))
      (Complex.exp (((d : ℂ) * a) * z) * ((d : ℂ) * a)) z :=
    (Complex.hasDerivAt_exp _).comp z hlin
  have hfun : (fun w : ℂ => Complex.exp (a * w) ^ d)
      = fun w : ℂ => Complex.exp (((d : ℂ) * a) * w) := funext hpow
  have hval : Complex.exp (((d : ℂ) * a) * z) * ((d : ℂ) * a)
      = a * (d : ℂ) * Complex.exp (a * z) ^ d := by
    rw [← hpow z]
    ring
  rw [hfun, ← hval]
  exact hcomp

/-- **Total differentiation realizes the derivative.** -/
theorem hasDerivAt_expJetEvalHom {a : ℂ} {h : ℂ → ℂ}
    (hh : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m h)) (F : ExpJetPoly) (z : ℂ) :
    HasDerivAt (fun w => expJetEvalHom a h w F) (expJetEvalHom a h z (expJetTotalDeriv a F)) z := by
  classical
  set M : ℕ := F.natDegree + 1 with hM
  have hFM : F.natDegree < M := Nat.lt_succ_self _
  have hDM : (expJetTotalDeriv a F).natDegree < M :=
    lt_of_le_of_lt (natDegree_expJetTotalDeriv_le a F) hFM
  have hfun : (fun w => expJetEvalHom a h w F)
      = fun w => ∑ d ∈ Finset.range M,
          MvPolynomial.eval (jetVector h w) (F.coeff d) * Complex.exp (a * w) ^ d := by
    funext w
    exact expJetEvalHom_eq_sum_range a h w hFM
  have hterm : ∀ d ∈ Finset.range M,
      HasDerivAt (fun w => MvPolynomial.eval (jetVector h w) (F.coeff d)
          * Complex.exp (a * w) ^ d)
        (MvPolynomial.eval (jetVector h z) ((expJetTotalDeriv a F).coeff d)
          * Complex.exp (a * z) ^ d) z := by
    intro d _
    have h1 := hasDerivAt_eval_jetVector hh (F.coeff d) z
    have h2 := hasDerivAt_exp_pow a d z
    have hprod := h1.mul h2
    have hval : MvPolynomial.eval (jetVector h z) (jetDeriv (F.coeff d))
          * Complex.exp (a * z) ^ d
        + MvPolynomial.eval (jetVector h z) (F.coeff d)
          * (a * (d : ℂ) * Complex.exp (a * z) ^ d)
        = MvPolynomial.eval (jetVector h z) ((expJetTotalDeriv a F).coeff d)
          * Complex.exp (a * z) ^ d := by
      rw [coeff_expJetTotalDeriv]
      simp only [map_add, map_mul, MvPolynomial.eval_C]
      ring
    rw [← hval]
    exact hprod
  have hsum := HasDerivAt.sum hterm
  have hfe : (∑ d ∈ Finset.range M, fun w =>
        MvPolynomial.eval (jetVector h w) (F.coeff d) * Complex.exp (a * w) ^ d)
      = fun w => ∑ d ∈ Finset.range M,
          MvPolynomial.eval (jetVector h w) (F.coeff d) * Complex.exp (a * w) ^ d := by
    funext w
    exact Finset.sum_apply w _ _
  rw [hfun, expJetEvalHom_eq_sum_range a h z hDM, ← hfe]
  exact hsum

theorem expJetEvalHom_expJetTotalDeriv_eq_zero {a : ℂ} {h : ℂ → ℂ}
    (hh : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m h)) {F : ExpJetPoly}
    (hF : ∀ z, expJetEvalHom a h z F = 0) (z : ℂ) :
    expJetEvalHom a h z (expJetTotalDeriv a F) = 0 := by
  have hd := hasDerivAt_expJetEvalHom (a := a) hh F z
  have hconst : (fun w => expJetEvalHom a h w F) = fun _ : ℂ => (0 : ℂ) := by
    funext w
    exact hF w
  have hzero : HasDerivAt (fun w => expJetEvalHom a h w F) 0 z := by
    rw [hconst]
    exact hasDerivAt_const z 0
  exact (hzero.unique hd).symm

/-! ### The descent -/

/-- **Elimination of the exponential.**  A nonzero relation between the jets of `h` and `exp (a z)`
yields a nonzero relation between the jets of `h` alone. -/
theorem exists_autonomousJet_of_expJetRelation {a : ℂ} (ha : a ≠ 0) {h : ℂ → ℂ}
    (hh : ∀ m : ℕ, Differentiable ℂ (iteratedDeriv m h)) {F : ExpJetPoly} (hF0 : F ≠ 0)
    (hF : ∀ z, expJetEvalHom a h z F = 0) :
    ∃ c : MvPolynomial ℕ ℂ, c ≠ 0 ∧ ∀ z, MvPolynomial.eval (jetVector h z) c = 0 := by
  classical
  suffices haux : ∀ D : ℕ, ∀ G : ExpJetPoly, G.natDegree ≤ D → G ≠ 0 →
      (∀ z, expJetEvalHom a h z G = 0) →
      ∃ c : MvPolynomial ℕ ℂ, c ≠ 0 ∧ ∀ z, MvPolynomial.eval (jetVector h z) c = 0 by
    exact haux F.natDegree F le_rfl hF0 hF
  intro D
  induction D using Nat.strong_induction_on with
  | _ D ih =>
    intro G hGD hG0 hG
    set d₀ : ℕ := G.natDegree with hd₀
    set cD : MvPolynomial ℕ ℂ := G.coeff d₀ with hcD
    have hcD0 : cD ≠ 0 := by
      rw [hcD, hd₀]
      exact Polynomial.leadingCoeff_ne_zero.2 hG0
    set q : MvPolynomial ℕ ℂ := jetDeriv cD + MvPolynomial.C (a * (d₀ : ℂ)) * cD with hq
    set H : ExpJetPoly :=
      Polynomial.C cD * expJetTotalDeriv a G - Polynomial.C q * G with hH
    have hHzero : ∀ z, expJetEvalHom a h z H = 0 := by
      intro z
      rw [hH, map_sub, map_mul, map_mul, hG z,
        expJetEvalHom_expJetTotalDeriv_eq_zero hh hG z, mul_zero, mul_zero, sub_zero]
    have hHcoeff : ∀ e, d₀ ≤ e → H.coeff e = 0 := by
      intro e he
      rcases eq_or_lt_of_le he with rfl | hlt
      · rw [hH, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          coeff_expJetTotalDeriv, ← hcD, hq]
        ring
      · have h0 : G.coeff e = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hH, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          coeff_expJetTotalDeriv, h0, map_zero, mul_zero, add_zero, mul_zero, mul_zero, sub_zero]
    by_cases hHne : H = 0
    · -- every lower coefficient of `G` vanishes, so `G` is a single monomial
      have hlow : ∀ e, e < d₀ → G.coeff e = 0 := by
        intro e he
        have hcoeff : H.coeff e = 0 := by rw [hHne, Polynomial.coeff_zero]
        rw [hH, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          coeff_expJetTotalDeriv, hq] at hcoeff
        have hrel : cD * jetDeriv (G.coeff e) - G.coeff e * jetDeriv cD
            = MvPolynomial.C ((d₀ - e : ℕ) * a) * (G.coeff e * cD) := by
          have hcast : ((d₀ : ℂ) - (e : ℂ)) = ((d₀ - e : ℕ) : ℂ) := by
            have : e ≤ d₀ := le_of_lt he
            push_cast [Nat.cast_sub this]
            ring
          have hexp : cD * (jetDeriv (G.coeff e) + MvPolynomial.C (a * (e : ℂ)) * G.coeff e)
              - (jetDeriv cD + MvPolynomial.C (a * (d₀ : ℂ)) * cD) * G.coeff e = 0 := hcoeff
          have hsplit : cD * jetDeriv (G.coeff e) - G.coeff e * jetDeriv cD
              = MvPolynomial.C (a * ((d₀ : ℂ) - (e : ℂ))) * (G.coeff e * cD) := by
            have hCsub : (MvPolynomial.C (a * ((d₀ : ℂ) - (e : ℂ))) : MvPolynomial ℕ ℂ)
                = MvPolynomial.C (a * (d₀ : ℂ)) - MvPolynomial.C (a * (e : ℂ)) := by
              rw [← map_sub]
              congr 1
              ring
            rw [hCsub]
            linear_combination hexp
          rw [hsplit, hcast]
          congr 2
          ring
        have hμ : ((d₀ - e : ℕ) : ℂ) * a ≠ 0 := by
          have hne : ((d₀ - e : ℕ) : ℂ) ≠ 0 := by
            have : d₀ - e ≠ 0 := by omega
            exact_mod_cast Nat.cast_ne_zero.mpr this
          exact mul_ne_zero hne ha
        exact eq_zero_of_jetLogDeriv_const hμ hcD0 hrel
      have hGmono : G = Polynomial.C cD * Polynomial.X ^ d₀ := by
        refine Polynomial.ext fun e => ?_
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        rcases lt_trichotomy e d₀ with hlt | rfl | hgt
        · rw [hlow e hlt, if_neg (by omega), mul_zero]
        · rw [if_pos rfl, mul_one, hcD]
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega), mul_zero]
      refine ⟨cD, hcD0, fun z => ?_⟩
      have hz := hG z
      rw [hGmono, map_mul, map_pow, expJetEvalHom_C, expJetEvalHom_X] at hz
      have hexpne : Complex.exp (a * z) ^ d₀ ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
      exact (mul_eq_zero.1 hz).resolve_right hexpne
    · have hd₀pos : 0 < d₀ := by
        by_contra hcon
        have hd0 : d₀ = 0 := by omega
        exact hHne (Polynomial.ext fun e => by
          rw [Polynomial.coeff_zero]
          exact hHcoeff e (by omega))
      have hHdeg : H.natDegree ≤ d₀ - 1 :=
        Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun e he => hHcoeff e (by omega)
      exact ih (d₀ - 1) (by omega) H hHdeg hHne hHzero

end

end GaloisForLFunctions.HTGeometry
