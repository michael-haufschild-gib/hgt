import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeSource
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Finite prime deletion of the completed theta source and its Mellin law

For the literal theta atoms `a_n(x) = e^{x/2} h(n e^x)` (`thetaCuspSourceTerm x n`) and every
complex `w` with `Re w > -5/2`,
`∫ e^{wx} a_n(x) dx = n^{-(w+1/2)} G(w)`, `G(w) = (w - 1/2) Γ(w/2 + 5/4) π^{-(w/2+1/4)}`.

The finite prime deletion `D_S = ∏_{p∈S} (1 - p^{-1/2} T_{log p})` is expanded over squarefree
products of `S`.  Its bilateral Laplace transform is multiplied by the finite Euler factor
`∏_{p∈S} (1 - p^{-1/2-w})`, and on the completed source it removes exactly the atoms whose labels
are divisible by a deleted prime.
-/

open MeasureTheory Set Complex

namespace RHTower

/-- Complex Mellin transform of the Gaussian `exp (-π t²)`. -/
theorem mellin_gaussian_pi (σ : ℂ) (hσ : 0 < σ.re) :
    mellin (fun t : ℝ => ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)) σ =
      (1 / 2 : ℂ) * (1 / (Real.pi : ℂ)) ^ (σ / 2) * Complex.Gamma (σ / 2) := by
  have h1 : mellin (fun t : ℝ => ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)) σ =
      mellin (fun t : ℝ => (fun u : ℝ => ((Real.exp (-Real.pi * u) : ℝ) : ℂ))
        (t ^ (2 : ℝ))) σ := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [Real.rpow_two]
  rw [h1, mellin_comp_rpow (fun u : ℝ => ((Real.exp (-Real.pi * u) : ℝ) : ℂ)) σ 2]
  have h2 : mellin (fun u : ℝ => ((Real.exp (-Real.pi * u) : ℝ) : ℂ)) (σ / (2 : ℝ)) =
      (1 / (Real.pi : ℂ)) ^ (σ / 2) * Complex.Gamma (σ / 2) := by
    unfold mellin
    have hre : 0 < (σ / 2).re := by
      simp
      linarith
    rw [← Complex.integral_cpow_mul_exp_neg_mul_Ioi hre Real.pi_pos]
    push_cast
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [smul_eq_mul]
    ring_nf
  rw [h2, abs_two, Complex.real_smul]
  push_cast
  ring


theorem mellinConvergent_gaussian_pi (σ : ℂ) (hσ : 0 < σ.re) :
    MellinConvergent (fun t : ℝ => ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)) σ := by
  unfold MellinConvergent
  rw [mellin_convergent_iff_norm subset_rfl measurableSet_Ioi
    (by fun_prop : AEStronglyMeasurable
      (fun t : ℝ => ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ)) (volume.restrict (Ioi 0)))]
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
    (s := σ.re - 1) (by linarith)).integrableOn (s := Ioi 0)
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- Complex Mellin transform of the normalized theta-cusp seed, valid for `Re s > -2`. -/
theorem mellin_thetaCuspSeed_complex (s : ℂ) (hs : -2 < s.re) :
    mellin (fun t : ℝ => (thetaCuspSeed t : ℂ)) s =
      (s - 1) * Complex.Gamma (s / 2 + 1) * (1 / (Real.pi : ℂ)) ^ (s / 2) := by
  set g : ℝ → ℂ := fun t => ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ) with hg
  have h4 : 0 < (s + 4).re := by simp; linarith
  have h2 : 0 < (s + 2).re := by simp; linarith
  have hA := mellinConvergent_gaussian_pi (s + 4) h4
  have hB := mellinConvergent_gaussian_pi (s + 2) h2
  have hpoint : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • (thetaCuspSeed t : ℂ) =
      (4 * (Real.pi : ℂ) ^ 2) * ((t : ℂ) ^ (s + 4 - 1) • g t) -
        (6 * (Real.pi : ℂ)) * ((t : ℂ) ^ (s + 2 - 1) • g t) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
    have e4 : (t : ℂ) ^ (s + 4 - 1) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ 4 := by
      rw [show s + 4 - 1 = (s - 1) + ((4 : ℕ) : ℂ) by push_cast; ring,
        Complex.cpow_add _ _ ht0, Complex.cpow_natCast]
    have e2 : (t : ℂ) ^ (s + 2 - 1) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ 2 := by
      rw [show s + 2 - 1 = (s - 1) + ((2 : ℕ) : ℂ) by push_cast; ring,
        Complex.cpow_add _ _ ht0, Complex.cpow_natCast]
    rw [e4, e2, hg]
    simp only [smul_eq_mul, thetaCuspSeed]
    push_cast
    ring
  have hsplit : mellin (fun t : ℝ => (thetaCuspSeed t : ℂ)) s =
      (4 * (Real.pi : ℂ) ^ 2) * mellin g (s + 4) - (6 * (Real.pi : ℂ)) * mellin g (s + 2) := by
    unfold mellin
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
      integral_sub (hA.const_mul _) (hB.const_mul _), integral_const_mul, integral_const_mul]
  rw [hsplit, hg, mellin_gaussian_pi _ h4, mellin_gaussian_pi _ h2]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpi' : (1 / (Real.pi : ℂ)) ≠ 0 := one_div_ne_zero hpi
  have hz1 : s / 2 + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  rw [show (s + 4) / 2 = (s / 2 + 1) + 1 by ring, show (s + 2) / 2 = s / 2 + 1 by ring,
    Complex.Gamma_add_one _ hz1,
    show s / 2 + 1 + 1 = s / 2 + ((2 : ℕ) : ℂ) by push_cast; ring,
    show s / 2 + 1 = s / 2 + ((1 : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_add _ _ hpi', Complex.cpow_add _ _ hpi', Complex.cpow_natCast,
    Complex.cpow_natCast]
  field_simp
  ring


theorem mellinConvergent_thetaCuspSeed_of_neg_two_lt (s : ℂ) (hs : -2 < s.re) :
    MellinConvergent (fun t : ℝ => (thetaCuspSeed t : ℂ)) s := by
  set g : ℝ → ℂ := fun t => ((Real.exp (-Real.pi * t ^ 2) : ℝ) : ℂ) with hg
  have h4 : 0 < (s + 4).re := by simp; linarith
  have h2 : 0 < (s + 2).re := by simp; linarith
  have hA := (mellinConvergent_gaussian_pi (s + 4) h4).const_mul (4 * (Real.pi : ℂ) ^ 2)
  have hB := (mellinConvergent_gaussian_pi (s + 2) h2).const_mul (6 * (Real.pi : ℂ))
  refine IntegrableOn.congr_fun (hA.sub hB) (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have e4 : (t : ℂ) ^ (s + 4 - 1) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ 4 := by
    rw [show s + 4 - 1 = (s - 1) + ((4 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ ht0, Complex.cpow_natCast]
  have e2 : (t : ℂ) ^ (s + 2 - 1) = (t : ℂ) ^ (s - 1) * (t : ℂ) ^ 2 := by
    rw [show s + 2 - 1 = (s - 1) + ((2 : ℕ) : ℂ) by push_cast; ring,
      Complex.cpow_add _ _ ht0, Complex.cpow_natCast]
  simp only [Pi.sub_apply, e4, e2, smul_eq_mul, thetaCuspSeed]
  push_cast
  ring

/-- Change of variables `t = exp x` for complex-valued integrands. -/
theorem integral_Ioi_comp_exp_complex (f : ℝ → ℂ) :
    (∫ t in Ioi (0 : ℝ), f t) = ∫ x : ℝ, (Real.exp x : ℂ) * f (Real.exp x) := by
  have hderiv : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv
    (Real.exp_injective.injOn) f
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, MeasureTheory.setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with x
  rw [abs_of_pos (Real.exp_pos x), Complex.real_smul]

theorem integrableOn_Ioi_iff_comp_exp_complex (f : ℝ → ℂ) :
    IntegrableOn f (Ioi (0 : ℝ)) ↔
      Integrable (fun x : ℝ => (Real.exp x : ℂ) * f (Real.exp x)) := by
  have hderiv : ∀ x ∈ (univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv
    (Real.exp_injective.injOn) f
  rw [Set.image_univ, Real.range_exp] at h
  rw [h, integrableOn_univ]
  apply integrable_congr
  filter_upwards with x
  rw [abs_of_pos (Real.exp_pos x), Complex.real_smul]

private theorem thetaDeletion_ofReal_exp_cpow (x : ℝ) (z : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ z = Complex.exp ((x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]

/-- The Gamma factor `G(w) = (w - 1/2) Γ(w/2 + 5/4) π^{-(w/2+1/4)}` of every theta atom. -/
noncomputable def thetaAtomMellinFactor (w : ℂ) : ℂ :=
  (w - 1 / 2) * Complex.Gamma (w / 2 + 5 / 4) * (1 / (Real.pi : ℂ)) ^ (w / 2 + 1 / 4)

private theorem thetaCuspSourceTerm_exp_form (w : ℂ) (n : ℕ) (x : ℝ) :
    Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ) =
      (Real.exp x : ℂ) * (((Real.exp x : ℝ) : ℂ) ^ (w + 1 / 2 - 1) •
        (thetaCuspSeed (n * Real.exp x) : ℂ)) := by
  rw [thetaDeletion_ofReal_exp_cpow, smul_eq_mul, thetaCuspSourceTerm, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_exp]
  rw [← mul_assoc, ← Complex.exp_add, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Every positive-integer theta atom is integrable against every complex exponential with
`Re w > -5/2`. -/
theorem integrable_cexp_mul_thetaCuspSourceTerm (w : ℂ) (hw : -(5 / 2) < w.re)
    (n : ℕ) (hn : 0 < n) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hconv := (MellinConvergent.comp_mul_left hnR).mpr
    (mellinConvergent_thetaCuspSeed_of_neg_two_lt (w + 1 / 2) (by simp; linarith))
  have h := (integrableOn_Ioi_iff_comp_exp_complex _).mp hconv
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [thetaCuspSourceTerm_exp_form]

/-- **Complex atom Mellin law.**  `∫ e^{wx} a_n(x) dx = n^{-(w+1/2)} G(w)` for `Re w > -5/2`. -/
theorem integral_cexp_mul_thetaCuspSourceTerm (w : ℂ) (hw : -(5 / 2) < w.re)
    (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)) =
      (n : ℂ) ^ (-(w + 1 / 2)) * thetaAtomMellinFactor w := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscale := mellin_comp_mul_left (fun t : ℝ => (thetaCuspSeed t : ℂ)) (w + 1 / 2) hnR
  have hform : (∫ x : ℝ, Complex.exp (w * x) * (thetaCuspSourceTerm x n : ℂ)) =
      mellin (fun t : ℝ => (thetaCuspSeed (n * t) : ℂ)) (w + 1 / 2) := by
    rw [mellin, integral_Ioi_comp_exp_complex]
    apply integral_congr_ae
    filter_upwards with x
    rw [thetaCuspSourceTerm_exp_form]
  rw [hform, hscale, mellin_thetaCuspSeed_complex _ (by simp; linarith), smul_eq_mul,
    thetaAtomMellinFactor]
  congr 1
  rw [show w + 1 / 2 - 1 = w - 1 / 2 by ring, show (w + 1 / 2) / 2 + 1 = w / 2 + 5 / 4 by ring,
    show (w + 1 / 2) / 2 = w / 2 + 1 / 4 by ring]


/-! ## Finite literal prime deletion -/

/-- Finite literal prime deletion `∏_{p ∈ S} (1 - p^{-1/2} T_{log p})`, expanded over the
squarefree products of `S`. -/
noncomputable def thetaPrimeDeletion (S : Finset ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ T ∈ S.powerset, (-1 : ℝ) ^ T.card *
    ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) * f (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ)))

theorem thetaPrimeDeletion_empty (f : ℝ → ℝ) : thetaPrimeDeletion ∅ f = f := by
  funext x
  simp [thetaPrimeDeletion]

/-- One more prime factor `1 - p^{-1/2} T_{log p}`. -/
theorem thetaPrimeDeletion_insert {p : ℕ} {S : Finset ℕ} (hp : 0 < p) (hS : ∀ q ∈ S, 0 < q)
    (hpS : p ∉ S) (f : ℝ → ℝ) (x : ℝ) :
    thetaPrimeDeletion (insert p S) f x =
      thetaPrimeDeletion S f x -
        (p : ℝ) ^ (-(1 / 2 : ℝ)) * thetaPrimeDeletion S f (x + Real.log p) := by
  classical
  unfold thetaPrimeDeletion
  rw [Finset.sum_powerset_insert hpS, sub_eq_add_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hpT : p ∉ T := fun h => hpS (Finset.mem_powerset.mp hT h)
  have hTpos : 0 < ∏ q ∈ T, q := Finset.prod_pos fun q hq => hS q (Finset.mem_powerset.mp hT hq)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hTR : (0 : ℝ) < ((∏ q ∈ T, q : ℕ) : ℝ) := by exact_mod_cast hTpos
  rw [Finset.prod_insert hpT, Finset.card_insert_of_notMem hpT, Nat.cast_mul,
    Real.mul_rpow hpR.le hTR.le, Real.log_mul hpR.ne' hTR.ne', pow_succ]
  rw [show x + (Real.log p + Real.log ((∏ q ∈ T, q : ℕ) : ℝ)) =
      x + Real.log p + Real.log ((∏ q ∈ T, q : ℕ) : ℝ) by ring]
  ring

private theorem natCast_cpow_eq_cexp {n : ℕ} (hn : 0 < n) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp (z * (Real.log n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn', mul_comm]
  congr 2
  rw [show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, ← Complex.ofReal_log (by positivity)]

/-- Translation multiplies a bilateral Laplace transform by `e^{-wc}`. -/
theorem integral_cexp_mul_comp_add (w : ℂ) (c : ℝ) (G : ℝ → ℂ) :
    (∫ x : ℝ, Complex.exp (w * x) * G (x + c)) =
      Complex.exp (-(w * c)) * ∫ y : ℝ, Complex.exp (w * y) * G y := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => Complex.exp (w * y) * G y) c
  rw [← h, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

theorem integrable_cexp_mul_comp_add {w : ℂ} (c : ℝ) {G : ℝ → ℂ}
    (hG : Integrable (fun y : ℝ => Complex.exp (w * y) * G y)) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * G (x + c)) := by
  have h := (hG.comp_add_right c).const_mul (Complex.exp (-(w * c)))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [← mul_assoc, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **Deletion Mellin law.**  For every complex `w` at which the source is exponentially
integrable, `L_w (D_S f) = ∏_{p∈S} (1 - p^{-1/2-w}) L_w f`. -/
theorem integral_cexp_mul_thetaPrimeDeletion (S : Finset ℕ) (hS : ∀ p ∈ S, 0 < p)
    (f : ℝ → ℝ) (w : ℂ) (hf : Integrable (fun x : ℝ => Complex.exp (w * x) * (f x : ℂ))) :
    Integrable (fun x : ℝ => Complex.exp (w * x) * (thetaPrimeDeletion S f x : ℂ)) ∧
      (∫ x : ℝ, Complex.exp (w * x) * (thetaPrimeDeletion S f x : ℂ)) =
        (∏ p ∈ S, (1 - (p : ℂ) ^ (-(1 / 2 : ℂ) - w))) *
          ∫ x : ℝ, Complex.exp (w * x) * (f x : ℂ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [thetaPrimeDeletion_empty, hf]
  | @insert p S hpS ih =>
    have hp : 0 < p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, 0 < q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    obtain ⟨hint, heq⟩ := ih hS'
    have hfun : (fun x : ℝ => Complex.exp (w * x) *
        (thetaPrimeDeletion (insert p S) f x : ℂ)) =
        fun x : ℝ => Complex.exp (w * x) * (thetaPrimeDeletion S f x : ℂ) -
          (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            (Complex.exp (w * x) * (thetaPrimeDeletion S f (x + Real.log p) : ℂ)) := by
      funext x
      rw [thetaPrimeDeletion_insert hp hS' hpS]
      push_cast
      ring
    have hshift := integrable_cexp_mul_comp_add (Real.log p)
      (G := fun y => (thetaPrimeDeletion S f y : ℂ)) hint
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hint.sub (hshift.const_mul _)
    · rw [hfun, integral_sub hint (hshift.const_mul _), integral_const_mul,
        integral_cexp_mul_comp_add w (Real.log p) (fun y => (thetaPrimeDeletion S f y : ℂ)),
        heq, Finset.prod_insert hpS]
      have hpow : (((p : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * Complex.exp (-(w * (Real.log p : ℂ))) =
          (p : ℂ) ^ (-(1 / 2 : ℂ) - w) := by
        rw [natCast_cpow_eq_cexp hp, Complex.ofReal_cpow (by positivity),
          show ((p : ℝ) : ℂ) = (p : ℂ) by norm_cast, natCast_cpow_eq_cexp hp,
          ← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [← hpow]
      ring


/-! ## Coprime atom expansion of the deleted source -/

/-- Atom scaling: `d^{-1/2} a_n(x + log d) = a_{dn}(x)`. -/
theorem rpow_neg_half_mul_thetaCuspSourceTerm_add_log {d : ℕ} (hd : 0 < d) (x : ℝ) (n : ℕ) :
    (d : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspSourceTerm (x + Real.log d) n =
      thetaCuspSourceTerm x (d * n) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold thetaCuspSourceTerm
  rw [Real.exp_add, Real.exp_log hdR, show (x + Real.log d) / 2 = x / 2 + Real.log d / 2 by ring,
    Real.exp_add]
  have hhalf : (d : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Real.log d / 2) = 1 := by
    rw [Real.rpow_def_of_pos hdR, ← Real.exp_add]
    rw [show Real.log d * (-(1 / 2 : ℝ)) + Real.log d / 2 = 0 by ring, Real.exp_zero]
  calc
    (d : ℝ) ^ (-(1 / 2 : ℝ)) *
        (Real.exp (x / 2) * Real.exp (Real.log d / 2) * thetaCuspSeed (n * (Real.exp x * d))) =
        ((d : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Real.log d / 2)) *
          (Real.exp (x / 2) * thetaCuspSeed (n * (Real.exp x * d))) := by ring
    _ = Real.exp (x / 2) * thetaCuspSeed (((d * n : ℕ) : ℝ) * Real.exp x) := by
      rw [hhalf, one_mul]
      push_cast
      ring_nf

theorem rpow_neg_half_mul_thetaCuspFullSource_add_log {d : ℕ} (hd : 0 < d) (x : ℝ) :
    (d : ℝ) ^ (-(1 / 2 : ℝ)) * thetaCuspFullSource (x + Real.log d) =
      ∑' m : ℕ, {m : ℕ | d ∣ m}.indicator (thetaCuspSourceTerm x) m := by
  rw [thetaCuspFullSource, ← tsum_mul_left]
  simp_rw [rpow_neg_half_mul_thetaCuspSourceTerm_add_log hd]
  have hinj : Function.Injective (fun n : ℕ => d * n) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hd h
  have hsupp : Function.support ({m : ℕ | d ∣ m}.indicator (thetaCuspSourceTerm x)) ⊆
      Set.range (fun n : ℕ => d * n) := by
    intro m hm
    have hdm : d ∣ m := by
      by_contra h
      exact hm (Set.indicator_of_notMem (show m ∉ {m : ℕ | d ∣ m} from h) _)
    obtain ⟨n, rfl⟩ := hdm
    exact ⟨n, rfl⟩
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro n
  rw [Set.indicator_of_mem (show d * n ∈ {m : ℕ | d ∣ m} from dvd_mul_right d n)]

/-- **Coprime atom expansion.**  Deleting a finite set of primes removes exactly the Gaussian
atoms whose integer labels are divisible by one of them. -/
theorem thetaPrimeDeletion_thetaCuspFullSource_eq_tsum (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (x : ℝ) :
    thetaPrimeDeletion S thetaCuspFullSource x =
      ∑' m : ℕ, {m : ℕ | ∀ p ∈ S, ¬ p ∣ m}.indicator (thetaCuspSourceTerm x) m := by
  classical
  have hsum := summable_thetaCuspSourceTerm x
  have hpos : ∀ T ∈ S.powerset, 0 < ∏ p ∈ T, p := fun T hT =>
    Finset.prod_pos fun p hp => (hS p (Finset.mem_powerset.mp hT hp)).pos
  unfold thetaPrimeDeletion
  have hterm : ∀ T ∈ S.powerset,
      (-1 : ℝ) ^ T.card * ((((∏ p ∈ T, p : ℕ)) : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspFullSource (x + Real.log ((∏ p ∈ T, p : ℕ) : ℝ))) =
        ∑' m : ℕ, (-1 : ℝ) ^ T.card *
          {m : ℕ | (∏ p ∈ T, p) ∣ m}.indicator (thetaCuspSourceTerm x) m := by
    intro T hT
    rw [rpow_neg_half_mul_thetaCuspFullSource_add_log (hpos T hT), tsum_mul_left]
  rw [Finset.sum_congr rfl hterm, ← Summable.tsum_finsetSum]
  · apply tsum_congr
    intro m
    have hfilter : ∀ T ∈ S.powerset,
        (-1 : ℝ) ^ T.card * {m : ℕ | (∏ p ∈ T, p) ∣ m}.indicator (thetaCuspSourceTerm x) m =
          (if T ⊆ S.filter (· ∣ m) then (-1 : ℝ) ^ T.card else 0) * thetaCuspSourceTerm x m := by
      intro T hT
      have hTS := Finset.mem_powerset.mp hT
      have hiff : (∏ p ∈ T, p) ∣ m ↔ T ⊆ S.filter (· ∣ m) := by
        constructor
        · intro h q hq
          exact Finset.mem_filter.mpr ⟨hTS hq,
            (Finset.dvd_prod_of_mem (fun p => p) hq).trans h⟩
        · intro h
          apply Finset.prod_primes_dvd m
          · intro q hq
            exact (hS q (hTS hq)).prime
          · intro q hq
            exact (Finset.mem_filter.mp (h hq)).2
      by_cases hdiv : (∏ p ∈ T, p) ∣ m
      · rw [Set.indicator_of_mem (by exact hdiv), if_pos (hiff.mp hdiv)]
      · rw [Set.indicator_of_notMem (by exact hdiv), if_neg (fun h => hdiv (hiff.mpr h))]
        ring
    rw [Finset.sum_congr rfl hfilter, ← Finset.sum_mul, ← Finset.sum_filter]
    have hset : Finset.filter (fun T => T ⊆ S.filter (· ∣ m)) S.powerset =
        (S.filter (· ∣ m)).powerset := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨h.trans (Finset.filter_subset _ _), h⟩
    have hpow : (∑ T ∈ (S.filter (· ∣ m)).powerset, (-1 : ℝ) ^ T.card) =
        if S.filter (· ∣ m) = ∅ then 1 else 0 := by
      have h := Finset.sum_powerset_neg_one_pow_card (x := S.filter (· ∣ m))
      have h' := congrArg (Int.cast : ℤ → ℝ) h
      push_cast at h'
      rw [h']
    rw [hset, hpow]
    by_cases hcop : ∀ p ∈ S, ¬ p ∣ m
    · have hempty : S.filter (· ∣ m) = ∅ := by
        ext q
        simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        exact hcop q
      rw [if_pos hempty, one_mul, Set.indicator_of_mem (by exact hcop)]
    · have hne : S.filter (· ∣ m) ≠ ∅ := by
        push Not at hcop
        obtain ⟨q, hq, hqm⟩ := hcop
        exact Finset.nonempty_iff_ne_empty.mp ⟨q, Finset.mem_filter.mpr ⟨hq, hqm⟩⟩
      rw [if_neg hne, zero_mul, Set.indicator_of_notMem (by exact hcop)]
  · intro T _
    exact (hsum.indicator _).mul_left _

end RHTower
