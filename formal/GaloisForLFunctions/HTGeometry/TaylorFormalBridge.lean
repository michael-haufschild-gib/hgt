import GaloisForLFunctions.HTGeometry.FormalHypertranscendence
import GaloisForLFunctions.HTGeometry.Hypertranscendence

/-!
# The analytic-to-formal Taylor bridge

The formal survival theorem `aeval_survives` speaks of the formal power series `aeval (formalJets n F) Q`.
An algebraic differential relation, by contrast, is the vanishing of the *function*
`z ↦ eval (z, f z, f'z, …) Q`.  This file bridges the two registers via the **Taylor map**

`taylorPS h = PowerSeries.mk (k ↦ iteratedDeriv k h 0 / k!)`,

the exponential-generating power series of the origin derivatives.  On smooth functions it is a ring
homomorphism commuting with the formal derivative `d⁄dX`, so it carries the jet substitution
`z ↦ eval(jets z) Q` to `aeval (formalJets n (taylorPS f)) Q` (`taylorPS_jetFun`).  Consequently a
function whose jet substitution vanishes identically has a vanishing formal substitution, which
`aeval_survives` forbids — giving `hypertranscendental_of_aeval_survives`.
-/

open PowerSeries Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions

/-- The Taylor (exponential generating) power series of `h` at the origin. -/
noncomputable def taylorPS (h : ℂ → ℂ) : ℂ⟦X⟧ := PowerSeries.mk (fun k => iteratedDeriv k h 0 / k !)

@[simp] theorem coeff_taylorPS (h : ℂ → ℂ) (k : ℕ) :
    coeff k (taylorPS h) = iteratedDeriv k h 0 / k ! := by rw [taylorPS, PowerSeries.coeff_mk]

/-- Smoothness is inherited by all iterated derivatives. -/
theorem contDiff_iteratedDeriv (j : ℕ) : ∀ {u : ℂ → ℂ}, ContDiff ℂ (⊤ : ℕ∞) u →
    ContDiff ℂ (⊤ : ℕ∞) (iteratedDeriv j u) := by
  induction j with
  | zero => intro u hu; simpa [iteratedDeriv_zero] using hu
  | succ j ih => intro u hu; rw [iteratedDeriv_succ']; exact ih hu.deriv'

theorem taylorPS_add {u v : ℂ → ℂ} (hu : ContDiff ℂ (⊤ : ℕ∞) u) (hv : ContDiff ℂ (⊤ : ℕ∞) v) :
    taylorPS (u + v) = taylorPS u + taylorPS v := by
  ext k
  rw [coeff_taylorPS, iteratedDeriv_add (hu.contDiffAt.of_le (by exact_mod_cast le_top))
    (hv.contDiffAt.of_le (by exact_mod_cast le_top)), map_add, coeff_taylorPS, coeff_taylorPS,
    add_div]

theorem taylorPS_mul {u v : ℂ → ℂ} (hu : ContDiff ℂ (⊤ : ℕ∞) u) (hv : ContDiff ℂ (⊤ : ℕ∞) v) :
    taylorPS (u * v) = taylorPS u * taylorPS v := by
  ext N
  rw [coeff_taylorPS, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_mul (hu.contDiffAt.of_le (by exact_mod_cast le_top))
      (hv.contDiffAt.of_le (by exact_mod_cast le_top)), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range, Nat.lt_succ_iff] at hi
  rw [coeff_taylorPS, coeff_taylorPS]
  have hfac : (N.choose i : ℂ) * (i ! : ℂ) * ((N - i)! : ℂ) = (N ! : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hi0 : (i ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hNi0 : ((N - i)! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (N - i)
  have hN0 : (N ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp
  rw [← hfac]; ring

theorem taylorPS_const (a : ℂ) : taylorPS (fun _ => a) = PowerSeries.C a := by
  ext k
  rw [coeff_taylorPS, PowerSeries.coeff_C]
  rcases k with _ | k
  · simp
  · rw [iteratedDeriv_succ']
    simp [deriv_const']

theorem taylorPS_id : taylorPS (fun z : ℂ => z) = PowerSeries.X := by
  ext k
  rw [coeff_taylorPS, PowerSeries.coeff_X]
  rcases k with _ | _ | k
  · simp [iteratedDeriv_zero]
  · rw [iteratedDeriv_one, deriv_id'']; norm_num
  · have h1 : iteratedDeriv (k + 1 + 1) (fun z : ℂ => z) = 0 := by
      rw [iteratedDeriv_succ', deriv_id'', iteratedDeriv_succ', deriv_const', iteratedDeriv_eq_iterate]
      exact Function.iterate_fixed (by simp) k
    rw [h1]; simp

theorem taylorPS_deriv (u : ℂ → ℂ) :
    taylorPS (deriv u) = (d⁄dX ℂ) (taylorPS u) := by
  ext k
  rw [coeff_taylorPS, PowerSeries.coeff_derivative, coeff_taylorPS, ← iteratedDeriv_succ',
    Nat.factorial_succ]
  have hk0 : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  push_cast
  field_simp

theorem taylorPS_iteratedDeriv (j : ℕ) : ∀ (f : ℂ → ℂ),
    taylorPS (iteratedDeriv j f) = (⇑(d⁄dX ℂ))^[j] (taylorPS f) := by
  induction j with
  | zero => intro f; simp [iteratedDeriv_zero]
  | succ j ih =>
    intro f
    rw [iteratedDeriv_succ', ih (deriv f), taylorPS_deriv, Function.iterate_succ_apply]

variable (f : ℂ → ℂ) (n : ℕ)

/-- The analytic jet substitution `z ↦ Q(z, f z, f'z, …, f⁽ⁿ⁾z)`. -/
noncomputable def jetFun (Q : MvPolynomial (Fin (n + 2)) ℂ) : ℂ → ℂ :=
  fun z => MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) Q

theorem jetFun_C (a : ℂ) : jetFun f n (C a) = fun _ => a := by
  funext z; simp [jetFun]

theorem jetFun_add (p q : MvPolynomial (Fin (n + 2)) ℂ) :
    jetFun f n (p + q) = jetFun f n p + jetFun f n q := by
  funext z; simp only [jetFun, map_add]; rfl

theorem jetFun_mul (p q : MvPolynomial (Fin (n + 2)) ℂ) :
    jetFun f n (p * q) = jetFun f n p * jetFun f n q := by
  funext z; simp only [jetFun, map_mul]; rfl

theorem jetFun_X_zero : jetFun f n (MvPolynomial.X 0) = fun z => z := by
  funext z; simp [jetFun]

theorem jetFun_X_succ (j : Fin (n + 1)) :
    jetFun f n (MvPolynomial.X j.succ) = iteratedDeriv (j : ℕ) f := by
  funext z; simp [jetFun]

/-- Every jet substitution of a smooth function is smooth. -/
theorem contDiff_jetFun (hf : ContDiff ℂ (⊤ : ℕ∞) f) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (jetFun f n Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [jetFun_C]; exact contDiff_const
  | add p q hp hq => rw [jetFun_add]; exact hp.add hq
  | mul_X p i hp =>
    rw [jetFun_mul]
    apply hp.mul
    induction i using Fin.cases with
    | zero => rw [jetFun_X_zero]; exact contDiff_id
    | succ j => rw [jetFun_X_succ]; exact contDiff_iteratedDeriv _ hf

/-- **Taylor bridge.**  The Taylor series of the jet substitution equals the formal substitution into
the derivative jets of the Taylor series `taylorPS f`. -/
theorem taylorPS_jetFun (hf : ContDiff ℂ (⊤ : ℕ∞) f) (Q : MvPolynomial (Fin (n + 2)) ℂ) :
    taylorPS (jetFun f n Q) = aeval (formalJets n (taylorPS f)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [jetFun_C, taylorPS_const, aeval_C]; rfl
  | add p q hp hq => rw [jetFun_add, taylorPS_add (contDiff_jetFun f n hf p)
      (contDiff_jetFun f n hf q), hp, hq, map_add]
  | mul_X p i hp =>
    rw [jetFun_mul, taylorPS_mul (contDiff_jetFun f n hf p) (contDiff_jetFun f n hf _), hp, map_mul]
    congr 1
    induction i using Fin.cases with
    | zero => rw [jetFun_X_zero, taylorPS_id, aeval_X, formalJets, Fin.cons_zero]
    | succ j => rw [jetFun_X_succ, taylorPS_iteratedDeriv, aeval_X, formalJets, Fin.cons_succ]

/-- **Analytic hypertranscendence from formal survival.**  If the Taylor series of a smooth `f`
survives every nonzero formal algebraic differential relation, then `f` is hypertranscendental. -/
theorem hypertranscendental_of_aeval_survives {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (hsurv : ∀ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ), Q ≠ 0 →
      aeval (formalJets n (taylorPS f)) Q ≠ 0) :
    Hypertranscendental f := by
  rintro ⟨n, Q, hQ, hrel⟩
  apply hsurv n Q hQ
  have hjz : jetFun f n Q = 0 := by funext z; exact hrel z
  rw [← taylorPS_jetFun f n hf Q, hjz, show (0 : ℂ → ℂ) = fun _ => (0 : ℂ) from rfl,
    taylorPS_const, map_zero]

/-- **Coefficient survival ⟹ hypertranscendence.**  If every nonzero formal algebraic differential
relation has *some* nonzero power-series coefficient after substitution, the smooth `f` is
hypertranscendental. -/
theorem hypertranscendental_of_diffPoly_coeff_ne_zero {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (hsurv : ∀ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ), Q ≠ 0 →
      ∃ N : ℕ, (PowerSeries.coeff N) (aeval (formalJets n (taylorPS f)) Q) ≠ 0) :
    Hypertranscendental f := by
  refine hypertranscendental_of_aeval_survives hf (fun n Q hQ => ?_)
  obtain ⟨N, hN⟩ := hsurv n Q hQ
  intro h0
  rw [h0, map_zero] at hN
  exact hN rfl

end GaloisForLFunctions
