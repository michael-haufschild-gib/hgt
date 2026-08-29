import GaloisForLFunctions.HTGeometry.NevanlinnaErrorNegligible
import GaloisForLFunctions.HTGeometry.FiniteZeroCounting
import GaloisForLFunctions.HTGeometry.MaxModulusCharacteristicBound
import GaloisForLFunctions.HTGeometry.RamificationTermBound

/-!
# A transcendental entire function takes some value infinitely often

The second main theorem in its classical form,

```text
(q − 2) · T(r,f) ≤ ∑_j N(r, a_j, f) + S(r,f) + O(1),
```

follows from the entire second main theorem once the leftover term `m(r, 1/f')` is converted by the
first main theorem into `T(r,f') ≤ 2T(r,f) + m(r,f'/f)`.

With five separated values, if every one of them had a finite preimage the counting functions would
all be logarithmic, forcing the characteristic itself to be logarithmic along the good radii — and a
function with a logarithmic characteristic along a sequence of radii is a polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn

/-- **The second main theorem in classical form.**  For an entire function and `q` pairwise
separated values,
`(q − 2)·T(r,f) ≤ ∑_j N(r, a_j, f) + ∑_j m(r, f'/(f − a_j)) + m(r, f'/f) + C`. -/
theorem exists_sub_two_characteristic_le_sum_logCounting {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {q : ℕ} (A : Fin q → ℂ) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ i j : Fin q, i ≠ j → δ ≤ ‖A i - A j‖)
    (hforder : ∀ z, meromorphicOrderAt f z ≠ ⊤) :
    ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r →
      (∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0) →
      ((q : ℝ) - 2) * characteristic f ⊤ r
        ≤ (∑ j, logCounting f (A j : WithTop ℂ) r)
          + (∑ j, proximity (fun z => deriv f z / (f z - A j)) ⊤ r)
          + proximity (fun z => deriv f z / f z) ⊤ r + C := by
  classical
  have hmf : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  obtain ⟨K, hK0, hsmt⟩ := exists_mul_characteristic_le_of_separated_entire A hδ hsep hf
  refine ⟨(q : ℝ) * K + (q : ℝ) * Real.posLog (2 / δ)
      + Real.posLog ((q : ℝ) * (2 / δ)) + Real.log 2 + Real.log (q : ℝ)
      + max |Real.log ‖deriv f 0‖| |Real.log ‖meromorphicTrailingCoeffAt (deriv f) 0‖|,
    fun r hr hcod => ?_⟩
  have hr0 : r ≠ 0 := by
    intro h
    rw [h] at hr
    linarith
  have h1 := hsmt r hr0 hcod
  have h2 := proximity_inv_top_le (g := deriv f)
    (fun z => ((hf.deriv).analyticAt z).meromorphicAt) (r := r)
  have h3 := smallGrowth_characteristic_deriv_le hmf hforder hr
  have h4 : 0 ≤ logCounting (deriv f) 0 r :=
    ValueDistribution.logCounting_nonneg (f := deriv f) (e := (0 : WithTop ℂ)) hr
  linarith

/-- **A transcendental entire function takes one of any five separated values infinitely often.** -/
theorem exists_infinite_preimage_of_not_polynomial {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z) :
    ∃ a : ℂ, {z : ℂ | f z = a}.Infinite := by
  classical
  -- `f` is not identically zero, so all orders are finite
  have hzero : ∃ z : ℂ, f z ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnp ⟨0, by simpa using hcon⟩
  obtain ⟨z₀, hz₀⟩ := hzero
  have hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hcon
    refine hz₀ ?_
    have hfan : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
    rw [meromorphicOrderAt_eq_top_iff] at hcon
    exact hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ z) hcon.frequently (Set.mem_univ z₀)
  -- five separated values
  set A : Fin 5 → ℂ := fun j => ((j : ℕ) : ℂ) with hA
  have hsep : ∀ i j : Fin 5, i ≠ j → (1 : ℝ) ≤ ‖A i - A j‖ := by
    intro i j hij
    have hne : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ≠ 0 := by
      rw [sub_ne_zero]
      intro hcon
      exact hij (Fin.ext (by exact_mod_cast hcon))
    have hdiff : A i - A j = ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : ℂ) := by
      rw [hA]
      push_cast
      ring
    rw [hdiff, Complex.norm_intCast]
    have h1 : (1 : ℤ) ≤ |((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| := Int.one_le_abs hne
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)| : ℤ) : ℝ) := by exact_mod_cast h1
    rw [Int.cast_abs] at h2
    simpa using h2
  by_contra hcon
  push_neg at hcon
  have hfinite : ∀ j : Fin 5, {z : ℂ | f z = A j}.Finite := fun j => hcon (A j)
  -- the shifted functions
  have hfa : ∀ j : Fin 5, ∀ z, meromorphicOrderAt (fun w => f w - A j) z ≠ ⊤ := by
    intro j z hcon2
    have hdiff : Differentiable ℂ fun w => f w - A j := hf.sub (differentiable_const _)
    have hfan : AnalyticOnNhd ℂ (fun w => f w - A j) Set.univ :=
      hdiff.differentiableOn.analyticOnNhd isOpen_univ
    rw [meromorphicOrderAt_eq_top_iff] at hcon2
    have hall := hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ z) hcon2.frequently
    have hconst : ∀ w : ℂ, f w = A j := by
      intro w
      have h := hall (Set.mem_univ w)
      simp only [Pi.zero_apply] at h
      linear_combination h
    exact hnp ⟨Polynomial.C (A j), by simpa using hconst⟩
  have hfd : ∀ z, meromorphicOrderAt (deriv f) z ≠ ⊤ := by
    intro z hcon2
    have hfan : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
    have hdan : AnalyticOnNhd ℂ (deriv f) Set.univ := hfan.deriv
    rw [meromorphicOrderAt_eq_top_iff] at hcon2
    have hall := hdan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ z) hcon2.frequently
    have hconst : ∀ x y : ℂ, f x = f y :=
      fun x y => is_const_of_deriv_eq_zero hf (fun w => by simpa using hall (Set.mem_univ w)) x y
    exact hnp ⟨Polynomial.C (f 0), fun z => by simpa using hconst z 0⟩
  have hcod : ∀ r : ℝ, ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv f z ≠ 0 := by
    intro r
    have hfan : AnalyticOnNhd ℂ f Set.univ := hf.differentiableOn.analyticOnNhd isOpen_univ
    have hdan : AnalyticOnNhd ℂ (deriv f) Set.univ := hfan.deriv
    have hmero : MeromorphicOn (deriv f) (sphere (0 : ℂ) |r|) :=
      fun x _ => (hdan x (Set.mem_univ x)).meromorphicAt
    exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hmero fun u _ => hfd u
  -- the counting functions are logarithmic
  have hNj : ∀ j : Fin 5, ∃ M C R₀ : ℝ, 0 ≤ M ∧ 1 ≤ R₀ ∧ ∀ r : ℝ, R₀ ≤ r →
      logCounting f (A j : WithTop ℂ) r ≤ M * Real.log r + C := by
    intro j
    have hdiff : Differentiable ℂ fun w => f w - A j := hf.sub (differentiable_const _)
    have hzeros : {z : ℂ | (fun w => f w - A j) z = 0} = {z : ℂ | f z = A j} := by
      ext z
      simp [sub_eq_zero]
    obtain ⟨M, C, R₀, hM, hR₀, hbnd⟩ :=
      exists_logCounting_le_of_finite_zeros hdiff (hfa j) (by rw [hzeros]; exact hfinite j)
    refine ⟨M, C, R₀, hM, hR₀, fun r hr => ?_⟩
    have heq : logCounting f (A j : WithTop ℂ) r
        = ValueDistribution.logCounting (fun w => f w - A j) 0 r := by
      simp [ValueDistribution.logCounting]
    rw [heq]
    exact hbnd r hr
  choose M C R₀ hM hR₀ hbnd using hNj
  -- the growth conditions
  obtain ⟨hTtop, hTlog⟩ := charMajorant_growth_of_not_polynomial hf hnp
  obtain ⟨rn, hrntop, hTeq, hneg⟩ :=
    exists_good_radii_error_negligible hf A hf0 hfa hTlog hTtop
  obtain ⟨Csmt, hsmt⟩ := exists_sub_two_characteristic_le_sum_logCounting hf A one_pos hsep hf0
  -- along the good radii the characteristic is logarithmic
  set Mtot : ℝ := ∑ j, M j with hMtot
  set Ctot : ℝ := ∑ j, C j with hCtot
  have hMtot0 : 0 ≤ Mtot := Finset.sum_nonneg fun j _ => hM j
  have hlog : ∀ᶠ n in atTop, characteristic f ⊤ (rn n) ≤ Mtot * Real.log (rn n) + (Ctot + Csmt) := by
    have hR₀ev : ∀ j : Fin 5, ∀ᶠ n in atTop, R₀ j ≤ rn n :=
      fun j => hrntop.eventually_ge_atTop (R₀ j)
    have hall : ∀ᶠ n in atTop, ∀ j : Fin 5, R₀ j ≤ rn n := by
      rw [Filter.eventually_all]
      exact hR₀ev
    filter_upwards [hall, hTeq, hneg 1 one_pos, hrntop.eventually_ge_atTop (1 : ℝ)]
      with n hn heq hng hr1
    have hsmtn := hsmt (rn n) hr1 (hcod (rn n))
    have hcount : (∑ j, logCounting f (A j : WithTop ℂ) (rn n))
        ≤ Mtot * Real.log (rn n) + Ctot := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 5))) =>
        hbnd j (rn n) (hn j))
      calc (∑ j, logCounting f (A j : WithTop ℂ) (rn n))
          ≤ ∑ j, (M j * Real.log (rn n) + C j) := this
        _ = Mtot * Real.log (rn n) + Ctot := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul, hMtot, hCtot]
    rw [heq] at hng
    have hq : ((5 : ℕ) : ℝ) - 2 = 3 := by norm_num
    rw [hq] at hsmtn
    have hT0 : 0 ≤ characteristic f ⊤ (rn n) := ValueDistribution.characteristic_nonneg hr1
    linarith
  -- hence `f` is a polynomial
  set Ktot : ℝ := Mtot + |Ctot + Csmt| with hKtot
  have hKtot0 : 0 ≤ Ktot := by
    rw [hKtot]
    have := abs_nonneg (Ctot + Csmt)
    linarith
  refine hnp (exists_polynomial_of_frequently_characteristic_le_log hf hKtot0 ?_)
  intro hne
  have hcomp := hrntop.eventually hne
  have hgood : ∀ᶠ n in atTop, characteristic f ⊤ (rn n) ≤ Ktot * Real.log (rn n) := by
    filter_upwards [hlog, hrntop.eventually_ge_atTop (Real.exp 1)] with n hn hr
    have hr1 : (1 : ℝ) ≤ rn n :=
      le_trans (le_trans (by norm_num) (Real.add_one_le_exp 1)) hr
    have hlogr : (1 : ℝ) ≤ Real.log (rn n) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact hr
    have habs : Ctot + Csmt ≤ |Ctot + Csmt| := le_abs_self _
    have hmul : |Ctot + Csmt| ≤ |Ctot + Csmt| * Real.log (rn n) := by
      nlinarith [abs_nonneg (Ctot + Csmt)]
    rw [hKtot]
    nlinarith [hn]
  obtain ⟨n, hn1, hn2⟩ := (hcomp.and hgood).exists
  exact hn1 hn2

end GaloisForLFunctions.HTGeometry
