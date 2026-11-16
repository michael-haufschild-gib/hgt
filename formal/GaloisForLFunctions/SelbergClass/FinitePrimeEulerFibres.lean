import GaloisForLFunctions.SelbergClass.RationalEulerTwinsCannotHavePositiveLogarithms
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.AlmostEveryPrimeSeesEveryRightZero

/-! # Prime Euler fibres avoid finite cancellations

Every nonzero Euler fibre contains infinitely many nonzeros of ξ. Fibres belonging
to distinct primes meet in at most one point, so polynomial factors at finitely
many other primes cannot cancel the whole fibre.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Set Topology
open scoped Classical
namespace GaloisForLFunctions.SelbergClass.FiniteEuler
open GaloisForLFunctions.InfiniteRankPurityTheory
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.BlackHoleRingdown
open _root_.RHTower

/-- Every vertical progression has a nonzero value of ξ outside any finite set of indices. -/
theorem exists_xi_ne_zero_progression_outside (ρ : ℂ) {T : ℝ} (hT : 0 < T)
    (E : Finset ℤ) :
    ∃ n : ℤ, n ∉ E ∧ xi (ρ + ((n * T : ℝ) : ℂ) * I) ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset E
  have hz := h n hn
  have hre (m : ℤ) : (ρ + ((m * T : ℝ) : ℂ) * I).re = ρ.re := by simp
  have h0 : 0 < ρ.re := by simpa only [hre] using re_pos_of_xi_eq_zero hz
  have h1 : ρ.re < 1 := by simpa only [hre] using re_lt_one_of_xi_eq_zero hz
  apply not_summable_norm_riemannZeta_div h0 h1 hT
  apply summable_of_ne_finset_zero (s := E)
  intro m hm
  have hzeta : riemannZeta (ρ + ((m * T : ℝ) : ℂ) * I) = 0 := by
    apply (xi_eq_zero_iff (by rw [hre]; exact h0) ?_).mp (h m hm)
    intro he
    have hr := congrArg Complex.re he
    rw [hre, Complex.one_re] at hr
    exact h1.ne hr
  rw [hzeta, zero_div, norm_zero]

/-- A positive Euler coordinate is constant on its vertical period lattice. -/
theorem eulerCoordinate_period {q : ℝ} (hq : 1 < q) (ρ : ℂ) (n : ℤ) :
    (q : ℂ) ^ (-(ρ + ((n * (2 * Real.pi / Real.log q) : ℝ) : ℂ) * I)) =
      (q : ℂ) ^ (-ρ) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have hl : (Real.log q : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  rw [Complex.cpow_def_of_ne_zero hq0, Complex.cpow_def_of_ne_zero hq0,
    ← Complex.ofReal_log (zero_lt_one.trans hq).le]
  have he : (Real.log q : ℂ) *
      (-(ρ + ((n * (2 * Real.pi / Real.log q) : ℝ) : ℂ) * I)) =
      (Real.log q : ℂ) * (-ρ) + ((-n : ℤ) : ℂ) * (2 * Real.pi * I) := by
    push_cast
    field_simp
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Every nonzero Euler fibre contains infinitely many points outside the zero divisor of ξ. -/
theorem infinite_euler_fibre_xi_ne_zero {q : ℝ} (hq : 1 < q) {u : ℂ} (hu : u ≠ 0) :
    {s : ℂ | (q : ℂ) ^ (-s) = u ∧ xi s ≠ 0}.Infinite := by
  obtain ⟨ρ, hρ, _⟩ := exists_zero_localFactor_not_zero hq hu
  let T : ℝ := 2 * Real.pi / Real.log q
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hT : 0 < T := by dsimp [T]; positivity
  let f : ℤ → ℂ := fun n => ρ + ((n * T : ℝ) : ℂ) * I
  have hf : Function.Injective f := by
    intro m n h
    have he := congrArg Complex.im h
    simp only [f, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at he
    exact_mod_cast mul_right_cancel₀ hT.ne' (add_left_cancel he)
  intro hfin
  have hpre : (f ⁻¹' {s : ℂ | (q : ℂ) ^ (-s) = u ∧ xi s ≠ 0}).Finite :=
    hfin.preimage hf.injOn
  obtain ⟨n, hn, hxi⟩ := exists_xi_ne_zero_progression_outside ρ hT hpre.toFinset
  apply hn
  apply hpre.mem_toFinset.mpr
  exact ⟨(eulerCoordinate_period hq ρ n).trans hρ, hxi⟩

/-- Two distinct prime Euler coordinates jointly separate all complex points. -/
theorem eulerCoordinates_separate {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {s t : ℂ} (hpst : (p : ℂ) ^ (-s) = (p : ℂ) ^ (-t))
    (hqst : (q : ℂ) ^ (-s) = (q : ℂ) ^ (-t)) : s = t := by
  by_contra hst
  have he (r : ℕ) (hr : r.Prime) (h : (r : ℂ) ^ (-s) = (r : ℂ) ^ (-t)) :
      frobEig (Real.log r) (1 / 2 - s) = frobEig (Real.log r) (1 / 2 - t) := by
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne_zero
    rw [Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hr0,
      ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity : (0 : ℝ) ≤ r)] at h
    simpa only [frobEig, show (1 / 2 - s) - 1 / 2 = -s by ring,
      show (1 / 2 - t) - 1 / 2 = -t by ring] using h
  exact hpq (subsingleton_resonantPrimes (by
    intro hh
    apply hst
    linear_combination -hh) ⟨hp, he p hp hpst⟩ ⟨hq, he q hq hqst⟩)

/-- A polynomial in another prime coordinate removes only finitely many points of a
fixed prime fibre. -/
theorem finite_euler_fibre_multiplier_zeros {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (u : ℂ) (W : Multiset ℂ) :
    {s : ℂ | (p : ℂ) ^ (-s) = u ∧ multiplier W ((q : ℂ) ^ (-s)) = 0}.Finite := by
  have hroot (a : ℂ) :
      {s : ℂ | (p : ℂ) ^ (-s) = u ∧ a * (q : ℂ) ^ (-s) = 1}.Subsingleton := by
    intro s hs t ht
    have ha : a ≠ 0 := by
      intro ha
      have he := hs.2
      rw [ha, zero_mul] at he
      exact zero_ne_one he
    exact eulerCoordinates_separate hp hq hpq (hs.1.trans ht.1.symm)
      (mul_left_cancel₀ ha (hs.2.trans ht.2.symm))
  apply (W.toFinset.finite_toSet.biUnion fun a _ => (hroot a).finite).subset
  intro s hs
  obtain ⟨a, ha, he⟩ := (multiplier_eq_zero_iff W _).mp hs.2
  simp only [Set.mem_iUnion, Finset.mem_coe, Multiset.mem_toFinset]
  exact ⟨a, ha, hs.1, he⟩

/-- A prime fibre has a ξ-nonzero point avoiding polynomial zeros at every other prime
in a prescribed finite family. -/
theorem exists_euler_fibre_avoiding {p : ℕ} (hp : p.Prime) {u : ℂ} (hu : u ≠ 0)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (W : ℕ → Multiset ℂ) :
    ∃ s : ℂ, (p : ℂ) ^ (-s) = u ∧ xi s ≠ 0 ∧
      ∀ q ∈ S, q ≠ p → multiplier (W q) ((q : ℂ) ^ (-s)) ≠ 0 := by
  let B : Set ℂ := ⋃ q ∈ S.erase p,
    {s : ℂ | (p : ℂ) ^ (-s) = u ∧ multiplier (W q) ((q : ℂ) ^ (-s)) = 0}
  have hB : B.Finite := (S.erase p).finite_toSet.biUnion fun q hq =>
    finite_euler_fibre_multiplier_zeros hp
      (hS q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq).symm u (W q)
  have hi : {s : ℂ | (p : ℂ) ^ (-s) = u ∧ xi s ≠ 0}.Infinite := by
    simpa only [Complex.ofReal_natCast] using
      infinite_euler_fibre_xi_ne_zero (by exact_mod_cast hp.one_lt : (1 : ℝ) < p) hu
  obtain ⟨s, hs, hnot⟩ := hi.exists_notMem_finset hB.toFinset
  refine ⟨s, hs.1, hs.2, fun q hq hqp hz => ?_⟩
  apply hnot
  apply hB.mem_toFinset.mpr
  simp only [B, Set.mem_iUnion]
  exact ⟨q, Finset.mem_erase.mpr ⟨hqp, hq⟩, hs.1, hz⟩

end GaloisForLFunctions.SelbergClass.FiniteEuler
