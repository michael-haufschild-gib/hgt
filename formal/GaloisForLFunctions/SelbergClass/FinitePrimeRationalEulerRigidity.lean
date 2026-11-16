import GaloisForLFunctions.SelbergClass.FinitePrimeEulerFibres
import GaloisForLFunctions.SelbergClass.FinitePrimeEulerLogarithms

/-! # Finite rational Euler edits cannot preserve positive logarithms

Prime-fibre separation removes every reduced denominator of an entire completed
identity. Logarithmic coefficient uniqueness then bounds numerator roots prime by
prime, and reflection excludes every remaining factor. More precisely, each
nontrivial edit forces negative logarithmic coefficients at arbitrarily large
powers of one edited prime.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Topology
open scoped Classical BigOperators
namespace GaloisForLFunctions.SelbergClass.FiniteEuler
open GaloisForLFunctions.InfiniteRankPurityTheory
open _root_.RHTower

/-- Reduced denominator roots cannot be cancelled by ξ or by factors at other primes. -/
theorem finite_denominator_eq_zero (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (W V : ℕ → Multiset ℂ) (c : ℂ) (F : ℂ → ℂ)
    (hV : ∀ p ∈ S, ∀ v ∈ V p, v ≠ 0)
    (hred : ∀ p ∈ S, ∀ v ∈ V p, v ∉ W p)
    (hid : ∀ s : ℂ, finiteMultiplier S V s * F s =
      Complex.exp (c * s) * finiteMultiplier S W s * xi s) :
    ∀ p ∈ S, V p = 0 := by
  intro p hp
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro v hv
  have hv0 := hV p hp v hv
  obtain ⟨s, hs, hxi, hother⟩ := exists_euler_fibre_avoiding (hS p hp)
    (inv_ne_zero hv0) S hS W
  have hlocal : multiplier (V p) ((p : ℂ) ^ (-s)) = 0 :=
    (multiplier_eq_zero_iff _ _).mpr ⟨v, hv, by rw [hs, mul_inv_cancel₀ hv0]⟩
  have hden : finiteMultiplier S V s = 0 := Finset.prod_eq_zero hp hlocal
  have hnum : finiteMultiplier S W s ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    by_cases hqp : q = p
    · subst q
      intro hz
      obtain ⟨a, ha, he⟩ := (multiplier_eq_zero_iff _ _).mp hz
      rw [hs] at he
      have hav : a = v := by
        calc a = (a * v⁻¹) * v := by rw [mul_assoc, inv_mul_cancel₀ hv0, mul_one]
             _ = v := by rw [he, one_mul]
      exact hred p hp v hv (hav ▸ ha)
    · exact hother q hq hqp
  have he := hid s
  rw [hden, zero_mul] at he
  exact (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hnum) hxi) he.symm

/-- Unit-disk local roots give no numerator zeros in the positive half-plane. -/
theorem multiplier_ne_zero_of_unit_roots {p : ℕ} (hp : p.Prime) (W : Multiset ℂ)
    (hunit : ∀ a ∈ W, ‖a‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    multiplier W ((p : ℂ) ^ (-s)) ≠ 0 := by
  intro hz
  obtain ⟨a, ha, he⟩ := (multiplier_eq_zero_iff _ _).mp hz
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (neg_neg_of_pos hs)
  have hle : ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hunit a ha) (norm_nonneg _)).trans_lt
      (by simpa only [one_mul] using hnorm)
  rw [he, norm_one] at hle
  exact lt_irrefl _ hle

/-- Reflection removes every numerator once all its local roots lie in the unit disk. -/
theorem finite_numerator_eq_zero_of_reflection (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (W : ℕ → Multiset ℂ) (c : ℂ) (F : ℂ → ℂ)
    (hW : ∀ p ∈ S, ∀ a ∈ W p, a ≠ 0)
    (hunit : ∀ p ∈ S, ∀ a ∈ W p, ‖a‖ ≤ 1)
    (hid : ∀ s : ℂ, F s = Complex.exp (c * s) * finiteMultiplier S W s * xi s)
    (hfe : ∀ s : ℂ, F (1 - s) = F s) : ∀ p ∈ S, W p = 0 := by
  intro p hp
  apply Multiset.eq_zero_iff_forall_notMem.mpr
  intro a ha
  have ha0 := hW p hp a ha
  obtain ⟨s, hs, hxi⟩ := exists_zero_localFactor_not_zero
    (by exact_mod_cast (hS p hp).one_lt : (1 : ℝ) < p) (inv_ne_zero ha0)
  simp only [Complex.ofReal_natCast] at hs
  have hlocal : multiplier (W p) ((p : ℂ) ^ (-s)) = 0 :=
    (multiplier_eq_zero_iff _ _).mpr ⟨a, ha, by rw [hs, mul_inv_cancel₀ ha0]⟩
  have hleft : s.re ≤ 0 := le_of_not_gt fun h =>
    multiplier_ne_zero_of_unit_roots (hS p hp) (W p) (hunit p hp) h hlocal
  have hzero : finiteMultiplier S W s = 0 := Finset.prod_eq_zero hp hlocal
  have hFs : F s = 0 := by rw [hid s, hzero, mul_zero, zero_mul]
  have hright : finiteMultiplier S W (1 - s) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    apply multiplier_ne_zero_of_unit_roots (hS q hq) (W q) (hunit q hq)
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have he := hid (1 - s)
  rw [hfe s, hFs, xi_one_sub] at he
  exact (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hright) hxi) he.symm

/-- Finite reduced rational prime edits preserving reflection and logarithmic positivity
have no numerator or denominator. -/
theorem finite_rational_twin_rigidity (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (W V : ℕ → Multiset ℂ) (c : ℂ) (F : ℂ → ℂ) (b : ℕ → ℂ) (B : ℝ)
    (hW : ∀ p ∈ S, ∀ a ∈ W p, a ≠ 0) (hV : ∀ p ∈ S, ∀ v ∈ V p, v ≠ 0)
    (hred : ∀ p ∈ S, ∀ v ∈ V p, v ∉ W p)
    (hid : ∀ s : ℂ, finiteMultiplier S V s * F s =
      Complex.exp (c * s) * finiteMultiplier S W s * xi s)
    (hfe : ∀ s : ℂ, F (1 - s) = F s) (hpos : ∀ n : ℕ, 0 ≤ (b n).re)
    (hb : ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = riemannZeta s * finiteMultiplier S W s /
        finiteMultiplier S V s) : (∀ p ∈ S, W p = 0) ∧ (∀ p ∈ S, V p = 0) := by
  have hVzero := finite_denominator_eq_zero S hS W V c F hV hred hid
  have hVm (s : ℂ) : finiteMultiplier S V s = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [hVzero p hp]
    simp only [multiplier, Multiset.map_zero, Multiset.prod_zero]
  simp only [hVm, one_mul, div_one] at hid hb
  exact ⟨finite_numerator_eq_zero_of_reflection S hS W c F hW
    (finite_norm_le_one_of_nonnegative_logarithm S W hS hpos hb) hid hfe, hVzero⟩

/-- Finite polynomial Euler multipliers are entire. -/
theorem differentiable_finiteMultiplier (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (W : ℕ → Multiset ℂ) : Differentiable ℂ (finiteMultiplier S W) := by
  have hlocal (p : ℕ) (hp : p.Prime) (U : Multiset ℂ) :
      Differentiable ℂ (fun s : ℂ => multiplier U ((p : ℂ) ^ (-s))) := by
    have hpow : Differentiable ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) :=
      differentiable_id.neg.const_cpow (.inl (by exact_mod_cast hp.ne_zero))
    induction U using Multiset.induction_on with
    | empty => simpa only [multiplier, Multiset.map_zero, Multiset.prod_zero] using
        (differentiable_const (1 : ℂ))
    | cons a U ih =>
      simp only [multiplier, Multiset.map_cons, Multiset.prod_cons]
      exact ((differentiable_const (1 : ℂ)).sub (hpow.const_mul a)).mul ih
  exact Differentiable.fun_finsetProd fun p hp => hlocal p (hS p hp) (W p)

/-- Entire continuation extends the completed finite-prime Euler identity globally. -/
theorem finite_completed_identity_of_halfplane (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (W V : ℕ → Multiset ℂ) (c : ℂ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) (B : ℝ)
    (hid : ∀ s : ℂ, B < s.re → finiteMultiplier S V s * F s =
      Complex.exp (c * s) * finiteMultiplier S W s * xi s) :
    ∀ s : ℂ, finiteMultiplier S V s * F s =
      Complex.exp (c * s) * finiteMultiplier S W s * xi s := by
  have hL := Complex.analyticOnNhd_univ_iff_differentiable.mpr
    ((differentiable_finiteMultiplier S hS V).mul hF)
  have hR := Complex.analyticOnNhd_univ_iff_differentiable.mpr
    ((((differentiable_id.const_mul c).cexp).mul (differentiable_finiteMultiplier S hS W)).mul
      xi_differentiable)
  have heq := hL.eq_of_eventuallyEq hR (z₀ := ((B + 1 : ℝ) : ℂ)) (by
    have hU : IsOpen {s : ℂ | B < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : ((B + 1 : ℝ) : ℂ) ∈ {s : ℂ | B < s.re} := by
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    filter_upwards [hU.mem_nhds hmem] with s hs
    exact hid s hs)
  exact fun s => congrFun heq s

/-- Every nontrivial finite rational edit with an entire reflected completion forces
negative logarithmic coefficients at arbitrarily large powers of one edited prime. -/
theorem finite_rational_twin_has_negative_prime_power_logs
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (W V : ℕ → Multiset ℂ)
    (c : ℂ) (F : ℂ → ℂ) (b : ℕ → ℂ) (B : ℝ)
    (hne : ∃ p ∈ S, W p ≠ 0 ∨ V p ≠ 0)
    (hW : ∀ p ∈ S, ∀ a ∈ W p, a ≠ 0) (hV : ∀ p ∈ S, ∀ v ∈ V p, v ≠ 0)
    (hred : ∀ p ∈ S, ∀ v ∈ V p, v ∉ W p) (hF : Differentiable ℂ F)
    (hfe : ∀ s : ℂ, F (1 - s) = F s)
    (hid : ∀ s : ℂ, B < s.re → finiteMultiplier S V s * F s =
      Complex.exp (c * s) * finiteMultiplier S W s * xi s)
    (hb : ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = riemannZeta s * finiteMultiplier S W s /
        finiteMultiplier S V s) :
    ∃ p ∈ S, ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ 0 < k ∧ (b (p ^ k)).re < 0 := by
  have hid' := finite_completed_identity_of_halfplane S hS W V c F hF B hid
  have hVzero := finite_denominator_eq_zero S hS W V c F hV hred hid'
  have hVm (s : ℂ) : finiteMultiplier S V s = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    rw [hVzero p hp]
    simp only [multiplier, Multiset.map_zero, Multiset.prod_zero]
  simp only [hVm, one_mul, div_one] at hid' hb
  have hex : ∃ p ∈ S, ∃ a ∈ W p, 1 < ‖a‖ := by
    by_contra h
    push Not at h
    have hWzero := finite_numerator_eq_zero_of_reflection S hS W c F hW h hid' hfe
    obtain ⟨p, hp, hne⟩ := hne
    exact hne.elim (fun h => h (hWzero p hp)) (fun h => h (hVzero p hp))
  obtain ⟨p, hp, a, ha, hlarge⟩ := hex
  refine ⟨p, hp, fun N => ?_⟩
  obtain ⟨k, hkN, hk, hneg⟩ := exists_negative_logCoeff (hS p hp) (W p) ha hlarge N
  refine ⟨k, hkN, hk, ?_⟩
  rw [finite_coeff_prime_pow_eq S W hS hb hp hk.ne']
  exact hneg

/-- No nontrivial reduced rational modification at finitely many rational primes has an
entire reflected completion and a nonnegative logarithmic Dirichlet representation. -/
theorem not_exists_nontrivial_positive_finite_rational_twin
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ¬ ∃ (W V : ℕ → Multiset ℂ) (c : ℂ) (F : ℂ → ℂ) (b : ℕ → ℂ) (B : ℝ),
      (∃ p ∈ S, W p ≠ 0 ∨ V p ≠ 0) ∧
      (∀ p ∈ S, ∀ a ∈ W p, a ≠ 0) ∧ (∀ p ∈ S, ∀ v ∈ V p, v ≠ 0) ∧
      (∀ p ∈ S, ∀ v ∈ V p, v ∉ W p) ∧ Differentiable ℂ F ∧
      (∀ s : ℂ, F (1 - s) = F s) ∧ (∀ n : ℕ, 0 ≤ (b n).re) ∧
      (∀ s : ℂ, B < s.re → finiteMultiplier S V s * F s =
        Complex.exp (c * s) * finiteMultiplier S W s * xi s) ∧
      (∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
        Complex.exp (LSeries b s) = riemannZeta s * finiteMultiplier S W s /
          finiteMultiplier S V s) := by
  rintro ⟨W, V, c, F, b, B, hne, hW, hV, hred, hF, hfe, hpos, hid, hb⟩
  obtain ⟨hWzero, hVzero⟩ := finite_rational_twin_rigidity S hS W V c F b B hW hV hred
    (finite_completed_identity_of_halfplane S hS W V c F hF B hid) hfe hpos hb
  obtain ⟨p, hp, h⟩ := hne
  exact h.elim (fun h => h (hWzero p hp)) (fun h => h (hVzero p hp))

end GaloisForLFunctions.SelbergClass.FiniteEuler
