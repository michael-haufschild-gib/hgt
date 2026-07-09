/-
# The exponential of a nonzero algebraic integer is transcendental (Hermite–Lindemann)

For a nonzero algebraic integer `β ∈ ℂ`, the value `exp β` is transcendental over `ℚ`.  This is the
single-exponential Hermite–Lindemann theorem, the algebraic base's counterpart to the arithmetic
prime bases: the archimedean generator `∂_s` sends every nonzero algebraic-integer input off the
algebraic numbers entirely.

`Mathlib` supplies only the analytic half of Lindemann–Weierstrass
(`LindemannWeierstrass.exp_polynomial_approx`).  The algebraic half is Hermite's argument, packaged
here in two stages.

`exp_symm_relation_ne` is the abstract Hermite contradiction: given a finite family of complex
"exponents" `E : ι → ℂ` and integer "coefficients" `c : ι → ℤ` whose exponent polynomial
`∏ (X − E i)` has integer coefficients, whose weighted symmetric sums `∑ c_i · h(E_i)` are integers
for every `h ∈ ℤ[X]`, satisfying the exponential relation `∑ c_i e^{E_i} = 0` and the nondegeneracy
`∑_{E_i = w} c_i ≠ 0` at an integer reference `w`, a contradiction follows.  The mechanism: shift by
the integer `w`, multiply by the analytic approximant `nₚ`, and estimate with `exp_polynomial_approx`
to force a nonzero integer of absolute value `< 1`.

`exp_algInt_transcendental` feeds this the conjugate-product relation.  Assume `γ = exp β` algebraic;
pick `P ∈ ℤ[X]` with `P(γ) = 0`, `P.coeff 0 ≠ 0`, degree `n`.  With `β = β₁, …, β_d` the complete
conjugate set, `∏_j P(e^{β_j}) = 0` (the `j = 1` factor vanishes).  Multiplying this relation by its
exponent-negated form gives `∑_{(κ,κ')} c_κ c_{κ'} e^{E_κ − E_{κ'}} = 0` with `E_κ = ∑_j κ_j β_j`,
`c_κ = ∏_j a_{κ_j}`.  The reference `w = 0` is now an integer, and its coefficient is the sum of
squares `∑_v (∑_{E_κ = v} c_κ)²`, nonzero because a generic real-linear functional makes the extreme
exponent uniquely attained with coefficient the pure product `a_0^{d−|·|} a_n^{|·|} ≠ 0`.
-/

import Mathlib
import GaloisForLFunctions.RHTower.SymmetricConjugateIntegral

open Polynomial MvPolynomial Filter Complex
open scoped Classical Nat
open GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

/-- **Abstract Hermite contradiction.**  A finite family of complex exponents `E : ι → ℂ` and integer
coefficients `c : ι → ℤ` such that the exponent polynomial `∏ (X − E i)` lifts to `ℤ[X]`, every
weighted sum `∑ c_i · aeval (E i) h` (`h ∈ ℤ[X]`) is an integer, the exponential relation
`∑ c_i e^{E_i} = 0` holds, and the coefficient sum over `{i : E i = w}` is nonzero for an integer
reference `w`, is contradictory.  Hermite's mechanism completing `exp_polynomial_approx`. -/
theorem exp_symm_relation_ne {ι : Type*} [Fintype ι] (E : ι → ℂ) (c : ι → ℤ) (w : ℤ)
    (hlift : (∏ i : ι, (Polynomial.X - Polynomial.C (E i))) ∈ Polynomial.lifts (Int.castRingHom ℂ))
    (hTint : ∀ h : ℤ[X], ∃ m : ℤ, ∑ i : ι, (c i : ℂ) * Polynomial.aeval (E i) h = (m : ℂ))
    (hrel : ∑ i : ι, (c i : ℂ) * Complex.exp (E i) = 0)
    (ha0 : (∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i = (w : ℂ)), c i) ≠ 0) : False := by
  set wc : ℂ := (w : ℂ) with hwc
  -- shifted relation
  have hrel2 : ∑ i : ι, (c i : ℂ) * Complex.exp (E i - wc) = 0 := by
    have hstep : ∑ i : ι, (c i : ℂ) * Complex.exp (E i - wc)
        = (∑ i : ι, (c i : ℂ) * Complex.exp (E i)) * Complex.exp (-wc) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mul_assoc, ← Complex.exp_add]; ring_nf
    rw [hstep, hrel, zero_mul]
  obtain ⟨P, hP⟩ := hlift
  have hP' : P.map (Int.castRingHom ℂ) = ∏ i : ι, (Polynomial.X - Polynomial.C (E i)) := hP
  set fsh : ℤ[X] := P.comp (Polynomial.X + Polynomial.C w) with hfsh
  have hfshmap : fsh.map (Int.castRingHom ℂ)
      = ∏ i : ι, (Polynomial.X - Polynomial.C (E i - wc)) := by
    rw [hfsh, Polynomial.map_comp, hP', Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
        Polynomial.prod_comp]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, hwc, Polynomial.C_sub]
    simp only [eq_intCast]; ring
  have hfsh0 : fsh ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hfshmap
    have hne : (∏ i : ι, (Polynomial.X - Polynomial.C (E i - wc))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero _)
    exact hne hfshmap.symm
  set k := fsh.natTrailingDegree with hk
  have hdvd : Polynomial.X ^ k ∣ fsh :=
    Polynomial.X_pow_dvd_iff.mpr (fun e he => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree he)
  obtain ⟨g, hg⟩ := hdvd
  have hg0 : g.coeff 0 ≠ 0 := by
    have hcoeff : fsh.coeff k = g.coeff 0 := by
      have := Polynomial.coeff_X_pow_mul g k 0; rwa [Nat.zero_add, ← hg] at this
    rw [← hcoeff]
    exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hfsh0
  have hgne : g ≠ 0 := by
    intro h; apply hfsh0; rw [hg, h, mul_zero]
  have hfactor : fsh.map (Int.castRingHom ℂ)
      = Polynomial.X ^ k * g.map (Int.castRingHom ℂ) := by
    rw [hg, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X]
  have hroot : ∀ i : ι, (E i - wc) ≠ 0 → (E i - wc) ∈ g.aroots ℂ := by
    intro i hne
    have hfr : (fsh.map (Int.castRingHom ℂ)).eval (E i - wc) = 0 := by
      rw [hfshmap, Polynomial.eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hfr
    have hgr : (g.map (Int.castRingHom ℂ)).eval (E i - wc) = 0 :=
      (mul_eq_zero.mp hfr).resolve_left (pow_ne_zero _ hne)
    rw [Polynomial.mem_aroots]
    refine ⟨hgne, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    convert hgr using 2
  set a0 : ℤ := ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i = wc), c i with ha0def
  have hsplit : (a0 : ℂ) + ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
      (c i : ℂ) * Complex.exp (E i - wc) = 0 := by
    have he : (a0 : ℂ) = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i = wc),
        (c i : ℂ) * Complex.exp (E i - wc) := by
      rw [ha0def]; push_cast
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.mem_filter] at hi
      rw [hi.2, sub_self, Complex.exp_zero, mul_one]
    rw [he, Finset.sum_filter_add_sum_filter_not]
    exact hrel2
  have ha0ne : a0 ≠ 0 := ha0
  -- ============ analytic finish ============
  have hg0e : g.eval 0 ≠ 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hg0
  obtain ⟨B, hB⟩ := LindemannWeierstrass.exp_polynomial_approx g hg0e
  have hsum_exp : ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
      (c i : ℂ) * Complex.exp (E i - wc) = -(a0 : ℂ) :=
    eq_neg_of_add_eq_zero_right hsplit
  set Cabs : ℝ := ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
      |((c i : ℤ) : ℝ)| with hCabs
  have hlim : Filter.Tendsto (fun p : ℕ => Cabs * (B ^ p / (p - 1)!)) Filter.atTop (nhds 0) := by
    have h1 := FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop (1 : ℝ) B 1
    have h2 : Filter.Tendsto (fun p : ℕ => B ^ p / (p - 1)!) Filter.atTop (nhds 0) := by simpa using h1
    simpa using h2.const_mul Cabs
  have hev : ∀ᶠ p : ℕ in Filter.atTop, Cabs * (B ^ p / (p - 1)!) < 1 :=
    hlim.eventually_lt_const (by norm_num)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨P₀, hP₀⟩ := hev
  obtain ⟨p, hp_gt, hp_prime⟩ :=
    Nat.exists_infinite_primes (max P₀ (max ((g.eval 0).natAbs + 1) (a0.natAbs + 1)))
  have hp_ge_P₀ : P₀ ≤ p := le_trans (le_max_left _ _) hp_gt
  have hp_gt_g : (g.eval 0).natAbs < p := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hp_gt; omega
  have hp_gt_a0 : a0.natAbs < p := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hp_gt; omega
  obtain ⟨n_p, hnp_ndvd, gp, hgp_deg, hgp_bound⟩ := hB p hp_gt_g hp_prime
  -- integer part via the symmetric-sum hypothesis
  have haevalcomp : ∀ i : ι, Polynomial.aeval (E i) (gp.comp (Polynomial.X - Polynomial.C w))
      = Polynomial.aeval (E i - wc) gp := by
    intro i
    rw [aeval_comp]
    congr 1
    simp [hwc]
  obtain ⟨T₀, hT₀⟩ := hTint (gp.comp (Polynomial.X - Polynomial.C w))
  have hT₀' : ∑ i : ι, (c i : ℂ) * Polynomial.aeval (E i - wc) gp = (T₀ : ℂ) := by
    rw [← hT₀]; refine Finset.sum_congr rfl (fun i _ => ?_); rw [haevalcomp i]
  have hev0 : Polynomial.aeval (0 : ℂ) gp = ((gp.eval 0 : ℤ) : ℂ) := by
    have h0 : ((0 : ℂ)) = (algebraMap ℤ ℂ) (0 : ℤ) := by simp
    rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]; simp
  have hTfull : (T₀ : ℂ) = (a0 : ℂ) * ((gp.eval 0 : ℤ) : ℂ)
      + ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
          (c i : ℂ) * Polynomial.aeval (E i - wc) gp := by
    rw [← hT₀', ← Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset ι) (fun i => E i = wc)]
    congr 1
    rw [ha0def]; push_cast; rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_filter] at hi
    rw [hi.2, sub_self, hev0]
  set T : ℤ := T₀ - a0 * gp.eval 0 with hT
  have hTcast : (T : ℂ) = ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
      (c i : ℂ) * Polynomial.aeval (E i - wc) gp := by
    rw [hT]; push_cast; rw [hTfull]; ring
  have hbound : ∀ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
      ‖(n_p : ℂ) * Complex.exp (E i - wc)
        - (p : ℂ) * Polynomial.aeval (E i - wc) gp‖ ≤ B ^ p / (p - 1)! := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hr : (E i - wc) ∈ g.aroots ℂ := hroot i (sub_ne_zero.mpr hi.2)
    have hb := hgp_bound hr
    rw [zsmul_eq_mul, nsmul_eq_mul] at hb
    exact hb
  set Iℤ : ℤ := a0 * n_p + (p : ℤ) * T with hIℤ
  set δfun : ι → ℂ := fun i => (((c i : ℤ) : ℂ))
      * ((n_p : ℂ) * Complex.exp (E i - wc)
        - (p : ℂ) * Polynomial.aeval (E i - wc) gp) with hδ
  have hkey : (Iℤ : ℂ) = - ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc), δfun i := by
    have expand : ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc), δfun i
        = (n_p : ℂ) * (∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
            (c i : ℂ) * Complex.exp (E i - wc))
          - (p : ℂ) * (∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
            (c i : ℂ) * Polynomial.aeval (E i - wc) gp) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hδ]; ring
    rw [expand, hsum_exp, ← hTcast, hIℤ]
    push_cast; ring
  have hnorm : ‖(Iℤ : ℂ)‖ < 1 := by
    rw [hkey, norm_neg]
    calc ‖∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc), δfun i‖
        ≤ ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc), ‖δfun i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => E i ≠ wc),
            |((c i : ℤ) : ℝ)| * (B ^ p / (p - 1)!) := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [hδ]
          simp only [norm_mul]
          gcongr
          · apply le_of_eq; rw [Complex.norm_intCast]
          · exact hbound i hi
      _ = Cabs * (B ^ p / (p - 1)!) := by rw [hCabs, ← Finset.sum_mul]
      _ < 1 := hP₀ p hp_ge_P₀
  have hI0 : Iℤ = 0 := by
    have habs : |(Iℤ : ℝ)| < 1 := by rw [← Complex.norm_intCast]; exact hnorm
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  have hdvd2 : (p : ℤ) ∣ a0 * n_p := by
    have heq : a0 * n_p = -((p : ℤ) * T) := by
      have := hI0; rw [hIℤ] at this; linarith
    rw [heq]; exact (Dvd.intro T rfl).neg_right
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_prime_int.dvd_mul.mp hdvd2 with h | h
  · have hdvdnat : p ∣ a0.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; rwa [Int.natAbs_natCast] at this
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr ha0ne) hdvdnat
    exact absurd hle (not_le.mpr hp_gt_a0)
  · exact hnp_ndvd h

/-- For a tuple `κ : Fin d → Fin (n+1)`, the multivariate exponent `∑ⱼ (κ j)·Xⱼ` transforms under
a variable permutation `σ` by precomposition: `rename σ (∑ⱼ (κ j)·Xⱼ) = ∑ⱼ (κ (σ⁻¹ j))·Xⱼ`. -/
private theorem rename_tupleExp {d n : ℕ} (σ : Equiv.Perm (Fin d)) (κ : Fin d → Fin (n+1)) :
    (MvPolynomial.rename σ) (∑ j : Fin d, (κ j : ℕ) • (MvPolynomial.X j : MvPolynomial (Fin d) ℤ))
    = ∑ j : Fin d, (κ (σ.symm j) : ℕ) • (MvPolynomial.X j : MvPolynomial (Fin d) ℤ) := by
  rw [map_sum]
  rw [← Equiv.sum_comp σ (fun j => (κ (σ.symm j) : ℕ) • (MvPolynomial.X j : MvPolynomial (Fin d) ℤ))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_nsmul, MvPolynomial.rename_X, Equiv.symm_apply_apply]

/-- Evaluating the multivariate exponent `∑ⱼ (κ j)·Xⱼ` at the conjugates `bb` yields the complex
exponent `∑ⱼ (κ j)·bbⱼ`. -/
private theorem aeval_tupleExp {d n : ℕ} (bb : Fin d → ℂ) (κ : Fin d → Fin (n+1)) :
    (MvPolynomial.aeval bb) (∑ j : Fin d, (κ j : ℕ) • (MvPolynomial.X j : MvPolynomial (Fin d) ℤ))
    = ∑ j : Fin d, (κ j : ℕ) • bb j := by
  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [map_nsmul, MvPolynomial.aeval_X]

/-- **The exponent-difference polynomial lifts to `ℤ[X]`.**  For the complete conjugate set `bb` of a
monic `μ ∈ ℤ[X]`, the polynomial `∏_{κ,κ'} (X − (E_κ − E_{κ'}))` — whose roots are the differences of
tuple exponents `E_κ = ∑ⱼ (κ j)·bbⱼ` — has integer coefficients.  Each coefficient is a symmetric
integer polynomial in `bb` (permuting the conjugates permutes the tuple pairs), hence an integer by
`symmetric_aeval_conj_isInt`. -/
private theorem tupleDiff_poly_lifts {d n : ℕ} (μ : ℤ[X]) (bb : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (bb j)) Finset.univ.val).prod
        = μ.map (Int.castRingHom ℂ)) :
    (∏ p : (Fin d → Fin (n+1)) × (Fin d → Fin (n+1)),
        (Polynomial.X - Polynomial.C ((∑ j, (p.1 j : ℕ) • bb j) - (∑ j, (p.2 j : ℕ) • bb j))))
      ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
  set R : Polynomial (MvPolynomial (Fin d) ℤ) :=
    ∏ p : (Fin d → Fin (n+1)) × (Fin d → Fin (n+1)),
      (Polynomial.X - Polynomial.C ((∑ j, (p.1 j : ℕ) • (MvPolynomial.X (R := ℤ) j))
        - (∑ j, (p.2 j : ℕ) • (MvPolynomial.X (R := ℤ) j)))) with hR
  have hsym : ∀ m, (R.coeff m).IsSymmetric := by
    intro m σ
    have hmap : R.map (MvPolynomial.rename σ).toRingHom = R := by
      rw [hR, Polynomial.map_prod]
      refine Finset.prod_nbij' (fun p => (p.1 ∘ σ.symm, p.2 ∘ σ.symm))
        (fun p => (p.1 ∘ σ, p.2 ∘ σ)) (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
        ?_ ?_ ?_
      · intro p _
        simp only [Function.comp_def, Equiv.symm_apply_apply, Prod.mk.eta]
      · intro p _
        simp only [Function.comp_def, Equiv.apply_symm_apply, Prod.mk.eta]
      · intro p _
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [rename_tupleExp, rename_tupleExp]
        simp only [Function.comp_def]
    calc MvPolynomial.rename σ (R.coeff m)
        = (R.map (MvPolynomial.rename σ).toRingHom).coeff m := by rw [Polynomial.coeff_map]; rfl
      _ = R.coeff m := by rw [hmap]
  have hmapβ : R.map (MvPolynomial.aeval bb).toRingHom
      = ∏ p : (Fin d → Fin (n+1)) × (Fin d → Fin (n+1)),
          (Polynomial.X - Polynomial.C ((∑ j, (p.1 j : ℕ) • bb j) - (∑ j, (p.2 j : ℕ) • bb j))) := by
    rw [hR, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [aeval_tupleExp, aeval_tupleExp]
  rw [← hmapβ, Polynomial.lifts_iff_coeff_lifts]
  intro m
  rw [Polynomial.coeff_map]
  obtain ⟨z, hz⟩ := symmetric_aeval_conj_isInt μ bb hβ (R.coeff m) (hsym m)
  exact ⟨z, by show (Int.castRingHom ℂ) z = MvPolynomial.aeval bb (R.coeff m); rw [hz]; simp⟩

/-- **The weighted exponent-difference sums are integers.**  For the complete conjugate set `bb` of a
monic `μ ∈ ℤ[X]`, integer coefficients `a`, and any `h ∈ ℤ[X]`, the sum
`∑_{κ,κ'} (∏ⱼ a_{κ j})(∏ⱼ a_{κ' j})·h(E_κ − E_{κ'})` is a rational integer.  It is the evaluation at
`bb` of a symmetric integer polynomial, hence an integer by `symmetric_aeval_conj_isInt`. -/
private theorem tupleDiff_sum_isInt {d n : ℕ} (μ : ℤ[X]) (bb : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (bb j)) Finset.univ.val).prod
        = μ.map (Int.castRingHom ℂ)) (a : ℕ → ℤ) (h : ℤ[X]) :
    ∃ m : ℤ, ∑ p : (Fin d → Fin (n+1)) × (Fin d → Fin (n+1)),
        (((∏ j, a (p.1 j)) * (∏ j, a (p.2 j)) : ℤ) : ℂ)
        * Polynomial.aeval ((∑ j, (p.1 j : ℕ) • bb j) - (∑ j, (p.2 j : ℕ) • bb j)) h = (m : ℂ) := by
  set Ψ : MvPolynomial (Fin d) ℤ :=
    ∑ p : (Fin d → Fin (n+1)) × (Fin d → Fin (n+1)),
      ((∏ j, a (p.1 j)) * (∏ j, a (p.2 j))) •
        Polynomial.aeval ((∑ j, (p.1 j : ℕ) • (MvPolynomial.X (R := ℤ) j))
          - (∑ j, (p.2 j : ℕ) • (MvPolynomial.X (R := ℤ) j))) h with hΨ
  have hΨsym : Ψ.IsSymmetric := by
    intro σ
    rw [hΨ, map_sum]
    refine Finset.sum_nbij' (fun p => (p.1 ∘ σ.symm, p.2 ∘ σ.symm))
      (fun p => (p.1 ∘ σ, p.2 ∘ σ)) (fun _ _ => Finset.mem_univ _) (fun _ _ => Finset.mem_univ _)
      ?_ ?_ ?_
    · intro p _; simp only [Function.comp_def, Equiv.symm_apply_apply, Prod.mk.eta]
    · intro p _; simp only [Function.comp_def, Equiv.apply_symm_apply, Prod.mk.eta]
    · intro p _
      rw [map_zsmul, ← Polynomial.aeval_algHom_apply, map_sub, rename_tupleExp, rename_tupleExp]
      simp only [Function.comp_def]
      rw [Equiv.prod_comp σ.symm (fun j => a (p.1 j)), Equiv.prod_comp σ.symm (fun j => a (p.2 j))]
  obtain ⟨m, hm⟩ := symmetric_aeval_conj_isInt μ bb hβ Ψ hΨsym
  refine ⟨m, ?_⟩
  rw [← hm, hΨ, map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [map_zsmul, ← Polynomial.aeval_algHom_apply, map_sub, aeval_tupleExp, aeval_tupleExp,
      zsmul_eq_mul]

/-- **Nondegeneracy of the squared relation at the integer reference `0`.**  For nonzero conjugates
`bb` and integer coefficients `a` with `a 0 ≠ 0` and `a n ≠ 0`, the coefficient sum over tuple pairs
with equal exponents, `∑_{E_κ = E_{κ'}} (∏ⱼ a_{κ j})(∏ⱼ a_{κ' j})`, is nonzero.  It equals the sum of
squares `∑_v (∑_{E_κ = v} ∏ⱼ a_{κ j})²`, which is positive because a generic real-linear functional
makes the extreme exponent uniquely attained, so its group coefficient is the pure product
`∏ⱼ a_{κ*_j} ≠ 0`. -/
private theorem tupleDiff_nondegenerate {d n : ℕ} (bb : Fin d → ℂ) (hbb : ∀ j, bb j ≠ 0)
    (a : ℕ → ℤ) (ha0 : a 0 ≠ 0) (han : a n ≠ 0) :
    (∑ p ∈ (Finset.univ : Finset ((Fin d → Fin (n+1)) × (Fin d → Fin (n+1)))).filter
        (fun p => (∑ j, (p.1 j : ℕ) • bb j) - (∑ j, (p.2 j : ℕ) • bb j) = 0),
      (∏ j, a (p.1 j)) * (∏ j, a (p.2 j))) ≠ 0 := by
  set Ecoef : (Fin d → Fin (n+1)) → ℤ := fun κ => ∏ j, a (κ j) with hEcoefdef
  set Eexp : (Fin d → Fin (n+1)) → ℂ := fun κ => ∑ j, (κ j : ℕ) • bb j with hEexpdef
  obtain ⟨t, ht⟩ : ∃ t : ℝ, ∀ j, (bb j).re + t * (bb j).im ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_forall, not_ne_iff] at hcon
    choose f hf using hcon
    obtain ⟨x, hx, y, hy, hxy, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
      (s := Finset.range (d + 1)) (t := (Finset.univ : Finset (Fin d)))
      (by simp) (f := fun i => f (i : ℝ)) (fun i _ => Finset.mem_univ _)
    set j := f (x : ℝ) with hj
    have e1 : (bb j).re + (x : ℝ) * (bb j).im = 0 := hf (x : ℝ)
    have e2 : (bb j).re + (y : ℝ) * (bb j).im = 0 := by rw [hfeq]; exact hf (y : ℝ)
    have him : (bb j).im = 0 := by
      have hsub : ((x : ℝ) - (y : ℝ)) * (bb j).im = 0 := by ring_nf; linarith [e1, e2]
      have hne : (x : ℝ) - (y : ℝ) ≠ 0 := by simp only [sub_ne_zero]; exact_mod_cast hxy
      exact (mul_eq_zero.mp hsub).resolve_left hne
    have hre : (bb j).re = 0 := by rw [him, mul_zero, add_zero] at e1; exact e1
    exact hbb j (Complex.ext hre him)
  set Lm : ℂ →ₗ[ℝ] ℝ := Complex.reLm + t • Complex.imLm with hLmdef
  have hLm : ∀ z : ℂ, Lm z = z.re + t * z.im := by
    intro z; rw [hLmdef, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]; rfl
  have hLne : ∀ j, Lm (bb j) ≠ 0 := by intro j; rw [hLm]; exact ht j
  have hLexp : ∀ κ : Fin d → Fin (n+1), Lm (Eexp κ) = ∑ j, ((κ j : ℕ) : ℝ) * Lm (bb j) := by
    intro κ; simp only [hEexpdef]; rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_); rw [map_nsmul, nsmul_eq_mul]
  set κstar : Fin d → Fin (n+1) := fun j => if 0 < Lm (bb j) then Fin.last n else 0 with hκstardef
  have huniq : ∀ κ : Fin d → Fin (n+1), Eexp κ = Eexp κstar → κ = κstar := by
    intro κ hκ
    have hL : ∑ j, ((κ j : ℕ) : ℝ) * Lm (bb j) = ∑ j, ((κstar j : ℕ) : ℝ) * Lm (bb j) := by
      rw [← hLexp, ← hLexp, hκ]
    have hterm : ∀ j, 0 ≤ (((κstar j : ℕ) : ℝ) - ((κ j : ℕ) : ℝ)) * Lm (bb j) := by
      intro j
      rcases lt_trichotomy (Lm (bb j)) 0 with hlt | heq | hgt
      · have hst0 : κstar j = 0 := by simp only [hκstardef]; exact if_neg (not_lt.mpr hlt.le)
        rw [hst0]
        simp only [Fin.val_zero, Nat.cast_zero, zero_sub]
        have hknn : (0:ℝ) ≤ ((κ j : ℕ):ℝ) := by positivity
        exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hknn) hlt.le
      · exact absurd heq (hLne j)
      · have hst : κstar j = Fin.last n := by simp only [hκstardef]; exact if_pos hgt
        rw [hst]
        simp only [Fin.val_last]
        have hle : ((κ j : ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (κ j).isLt
        exact mul_nonneg (by linarith) (le_of_lt hgt)
    have hsum0 : ∑ j, (((κstar j : ℕ) : ℝ) - ((κ j : ℕ) : ℝ)) * Lm (bb j) = 0 := by
      simp only [sub_mul]
      rw [Finset.sum_sub_distrib, hL, sub_self]
    have heach : ∀ j ∈ Finset.univ, (((κstar j : ℕ) : ℝ) - ((κ j : ℕ) : ℝ)) * Lm (bb j) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm j)).mp hsum0
    funext j
    have hj := heach j (Finset.mem_univ j)
    have hz0 : ((κstar j : ℕ) : ℝ) - ((κ j : ℕ) : ℝ) = 0 :=
      (mul_eq_zero.mp hj).resolve_right (hLne j)
    have hval : (κstar j : ℕ) = (κ j : ℕ) := by
      have : ((κstar j : ℕ) : ℝ) = ((κ j : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    exact (Fin.val_injective hval).symm
  set C : ℂ → ℤ := fun v => ∑ κ ∈ Finset.univ.filter (fun κ => Eexp κ = v), Ecoef κ with hCdef
  set vals : Finset ℂ := Finset.univ.image Eexp with hvalsdef
  have hfilterstar : Finset.univ.filter (fun κ => Eexp κ = Eexp κstar) = {κstar} := by
    apply Finset.ext; intro κ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => huniq κ h, fun h => by rw [h]⟩
  have hCstar : C (Eexp κstar) = Ecoef κstar := by
    simp only [hCdef]; rw [hfilterstar, Finset.sum_singleton]
  have hEcoefstar : Ecoef κstar ≠ 0 := by
    simp only [hEcoefdef]
    rw [Finset.prod_ne_zero_iff]
    intro j _
    rcases lt_trichotomy (Lm (bb j)) 0 with hlt | heq | hgt
    · have hz : κstar j = 0 := by simp only [hκstardef]; exact if_neg (not_lt.mpr hlt.le)
      rw [hz]; simpa using ha0
    · exact absurd heq (hLne j)
    · have hz : κstar j = Fin.last n := by simp only [hκstardef]; exact if_pos hgt
      rw [hz]; simpa [Fin.val_last] using han
  have hfiltereq : (Finset.univ : Finset ((Fin d → Fin (n+1)) × (Fin d → Fin (n+1)))).filter
      (fun p => Eexp p.1 - Eexp p.2 = 0) = Finset.univ.filter (fun p => Eexp p.1 = Eexp p.2) := by
    apply Finset.filter_congr; intro p _; simp only [sub_eq_zero]
  have hD1 : (∑ p ∈ (Finset.univ : Finset ((Fin d → Fin (n+1)) × (Fin d → Fin (n+1)))).filter
      (fun p => Eexp p.1 = Eexp p.2), Ecoef p.1 * Ecoef p.2)
      = ∑ κ, Ecoef κ * C (Eexp κ) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun κ _ => ?_)
    simp only [hCdef]
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun κ' _ => ?_)
    rw [mul_ite, mul_zero]
    by_cases h : Eexp κ = Eexp κ'
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hD2 : (∑ κ, Ecoef κ * C (Eexp κ)) = ∑ v ∈ vals, (C v) ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to
        (fun κ (_ : κ ∈ Finset.univ) => Finset.mem_image_of_mem Eexp (Finset.mem_univ κ))
        (fun κ => Ecoef κ * C (Eexp κ))]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hstep : ∀ κ ∈ Finset.univ.filter (fun κ => Eexp κ = v),
        Ecoef κ * C (Eexp κ) = C v * Ecoef κ := by
      intro κ hκ; rw [Finset.mem_filter] at hκ; rw [hκ.2, mul_comm]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    have hCv : (∑ κ ∈ Finset.univ.filter (fun κ => Eexp κ = v), Ecoef κ) = C v := by
      simp only [hCdef]
    rw [hCv, sq]
  have hpos : 0 < ∑ v ∈ vals, (C v) ^ 2 := by
    refine Finset.sum_pos' (fun v _ => sq_nonneg _) ⟨Eexp κstar, ?_, ?_⟩
    · exact Finset.mem_image_of_mem Eexp (Finset.mem_univ κstar)
    · rw [hCstar]; positivity
  show (∑ p ∈ (Finset.univ : Finset ((Fin d → Fin (n+1)) × (Fin d → Fin (n+1)))).filter
      (fun p => Eexp p.1 - Eexp p.2 = 0), Ecoef p.1 * Ecoef p.2) ≠ 0
  rw [hfiltereq, hD1, hD2]
  exact ne_of_gt hpos

/-- **Hermite–Lindemann (single exponential).**  The exponential of a nonzero algebraic integer `β` is
transcendental over `ℚ`.  Assume `γ = exp β` is algebraic; pick `P ∈ ℤ[X]` with `P(γ) = 0`,
`P.coeff 0 ≠ 0`, degree `n`, and let `β = β₁, …, β_d` be the complete conjugate set of `minpoly ℤ β`.
Then `∏ⱼ P(exp βⱼ) = 0` (the `j = 1` factor vanishes); multiplying this relation by its
exponent-negated form gives `∑_{κ,κ'} c_κ c_{κ'} e^{E_κ − E_{κ'}} = 0` with `E_κ = ∑ⱼ (κ j)·βⱼ` and
`c_κ = ∏ⱼ a_{κ j}`.  At the integer reference `0` the coefficient sum is the positive sum of squares
`∑_v (∑_{E_κ = v} c_κ)²`; `exp_symm_relation_ne` then yields a contradiction. -/
theorem exp_algInt_transcendental {β : ℂ} (hβ : IsIntegral ℤ β) (hβ0 : β ≠ 0) :
    Transcendental ℚ (Complex.exp β) := by
  have hZ : Transcendental ℤ (Complex.exp β) := by
    intro halg
    set γ := Complex.exp β with hγ
    have hγ0 : γ ≠ 0 := Complex.exp_ne_zero β
    obtain ⟨P, hP0, hc0, hPev⟩ :
        ∃ P : ℤ[X], P ≠ 0 ∧ P.coeff 0 ≠ 0 ∧ (Polynomial.aeval γ) P = 0 := by
      obtain ⟨q, hq0, hqev⟩ := halg
      set m := q.natTrailingDegree with hm
      obtain ⟨P, hPq⟩ : Polynomial.X ^ m ∣ q :=
        Polynomial.X_pow_dvd_iff.mpr
          (fun e he => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree he)
      have hcoeff : q.coeff m = P.coeff 0 := by
        have := Polynomial.coeff_X_pow_mul P m 0; rwa [Nat.zero_add, ← hPq] at this
      refine ⟨P, ?_, ?_, ?_⟩
      · rintro rfl; rw [mul_zero] at hPq; exact hq0 hPq
      · rw [← hcoeff]; exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq0
      · have hfac : (Polynomial.aeval γ) q = γ ^ m * (Polynomial.aeval γ) P := by
          rw [hPq]; push_cast [map_mul, map_pow, Polynomial.aeval_X]; ring
        rw [hqev] at hfac
        exact (mul_eq_zero.mp hfac.symm).resolve_left (pow_ne_zero _ hγ0)
    set n := P.natDegree with hndef
    set a : ℕ → ℤ := fun k => P.coeff k with hadef
    have hazero : a 0 ≠ 0 := hc0
    have han : a n ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP0
    set μ := minpoly ℤ β with hμdef
    have hμmonic : μ.Monic := minpoly.monic hβ
    have hqmonic : (μ.map (Int.castRingHom ℂ)).Monic := hμmonic.map _
    have hqdeg : (μ.map (Int.castRingHom ℂ)).natDegree = μ.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℂ)) _
    have hcard : Multiset.card (μ.map (Int.castRingHom ℂ)).roots = μ.natDegree := by
      rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), hqdeg]
    obtain ⟨l, hl⟩ := Quotient.exists_rep (μ.map (Int.castRingHom ℂ)).roots
    have hmap : Multiset.map l.get Finset.univ.val = (μ.map (Int.castRingHom ℂ)).roots := by
      rw [Fin.univ_val_map, List.ofFn_get]; exact hl
    have hβprod :
        (Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val).prod
          = μ.map (Int.castRingHom ℂ) := by
      have hrw : (Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val)
          = (μ.map (Int.castRingHom ℂ)).roots.map (fun a => Polynomial.X - Polynomial.C a) := by
        rw [← hmap, Multiset.map_map]; rfl
      rw [hrw, prod_multiset_X_sub_C_of_monic_of_roots_card_eq hqmonic (hcard.trans hqdeg.symm)]
    have hβroot : β ∈ (μ.map (Int.castRingHom ℂ)).roots := by
      rw [Polynomial.mem_roots']
      refine ⟨hqmonic.ne_zero, ?_⟩
      rw [Polynomial.IsRoot.def, Polynomial.eval_map]
      have hh := minpoly.aeval ℤ β
      rw [Polynomial.aeval_def] at hh; exact hh
    have hβmem : β ∈ Multiset.map l.get Finset.univ.val := by rw [hmap]; exact hβroot
    obtain ⟨j₀, _, hj₀⟩ := Multiset.mem_map.mp hβmem
    set bb : Fin l.length → ℂ := l.get with hbbdef
    have hcoeff0 : μ.coeff 0 ≠ 0 := by
      intro hc0'
      obtain ⟨hpoly, hh⟩ := Polynomial.X_dvd_iff.mpr hc0'
      have haev : (Polynomial.aeval β) μ = 0 := minpoly.aeval ℤ β
      rw [hh, map_mul, Polynomial.aeval_X] at haev
      have haevh : (Polynomial.aeval β) hpoly = 0 := (mul_eq_zero.mp haev).resolve_left hβ0
      have hdvd2 : μ ∣ hpoly := minpoly.isIntegrallyClosed_dvd hβ haevh
      have hh0 : hpoly ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hμmonic.ne_zero hh
      have hdeg : μ.natDegree ≤ hpoly.natDegree := Polynomial.natDegree_le_of_dvd hdvd2 hh0
      have hdeg2 : hpoly.natDegree < μ.natDegree := by
        rw [hh, Polynomial.natDegree_mul (Polynomial.X_ne_zero) hh0, Polynomial.natDegree_X]; omega
      omega
    have hbbne : ∀ j, bb j ≠ 0 := by
      intro j hbj
      have hjmem : bb j ∈ (μ.map (Int.castRingHom ℂ)).roots := by
        rw [← hmap]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ j)
      rw [hbj] at hjmem
      have hev0 : (μ.map (Int.castRingHom ℂ)).eval 0 = 0 := (Polynomial.mem_roots'.mp hjmem).2
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map, Int.coe_castRingHom,
          Int.cast_eq_zero] at hev0
      exact hcoeff0 hev0
    have hzero : (∑ k : Fin (n+1), (a (k:ℕ):ℂ) * Complex.exp ((k:ℕ) • bb j₀)) = 0 := by
      have hconv : (∑ k : Fin (n+1), (a (k:ℕ):ℂ) * Complex.exp ((k:ℕ) • bb j₀))
          = ∑ k ∈ Finset.range (n+1), (a k:ℂ) * γ ^ k := by
        rw [Fin.sum_univ_eq_sum_range (fun m => (a m:ℂ) * Complex.exp (m • bb j₀)) (n+1)]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hj₀, Complex.exp_nsmul, ← hγ]
      rw [hconv]
      have haeval : (Polynomial.aeval γ) P = ∑ k ∈ Finset.range (n+1), (a k:ℂ) * γ ^ k := by
        rw [Polynomial.aeval_eq_sum_range, ← hndef]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [zsmul_eq_mul]
      rw [← haeval, hPev]
    have hA : (∑ κ : Fin l.length → Fin (n+1),
        ((∏ j, a (κ j):ℤ):ℂ) * Complex.exp (∑ j, (κ j:ℕ) • bb j)) = 0 := by
      have hAprod : (∑ κ : Fin l.length → Fin (n+1),
          ((∏ j, a (κ j):ℤ):ℂ) * Complex.exp (∑ j, (κ j:ℕ) • bb j))
          = ∏ j : Fin l.length, ∑ k : Fin (n+1), (a (k:ℕ):ℂ) * Complex.exp ((k:ℕ) • bb j) := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
        refine Finset.sum_congr rfl (fun κ _ => ?_)
        rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
        push_cast; ring
      rw [hAprod]
      exact Finset.prod_eq_zero (Finset.mem_univ j₀) hzero
    refine exp_symm_relation_ne
      (fun p : (Fin l.length → Fin (n+1)) × (Fin l.length → Fin (n+1)) =>
        (∑ j, (p.1 j:ℕ) • bb j) - (∑ j, (p.2 j:ℕ) • bb j))
      (fun p => (∏ j, a (p.1 j)) * (∏ j, a (p.2 j)))
      (0 : ℤ)
      (tupleDiff_poly_lifts μ bb hβprod)
      (fun h => tupleDiff_sum_isInt μ bb hβprod a h)
      ?_ ?_
    · have hfactor : (∑ p : (Fin l.length → Fin (n+1)) × (Fin l.length → Fin (n+1)),
          (((∏ j, a (p.1 j)) * (∏ j, a (p.2 j)):ℤ):ℂ)
            * Complex.exp ((∑ j, (p.1 j:ℕ) • bb j) - (∑ j, (p.2 j:ℕ) • bb j)))
          = (∑ κ : Fin l.length → Fin (n+1),
              ((∏ j, a (κ j):ℤ):ℂ) * Complex.exp (∑ j, (κ j:ℕ) • bb j))
            * (∑ κ' : Fin l.length → Fin (n+1),
                ((∏ j, a (κ' j):ℤ):ℂ) * Complex.exp (-(∑ j, (κ' j:ℕ) • bb j))) := by
        rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun κ _ => ?_)
        refine Finset.sum_congr rfl (fun κ' _ => ?_)
        push_cast
        rw [mul_mul_mul_comm, ← Complex.exp_add, sub_eq_add_neg]
      rw [hfactor, hA, zero_mul]
    · simpa only [Int.cast_zero] using tupleDiff_nondegenerate bb hbbne a hazero han
  exact fun hq => hZ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hq)

/-- **Hermite–Lindemann (algebraic exponent).**  The exponential of any nonzero algebraic number `β`
(algebraic over `ℤ`, equivalently over `ℚ`) is transcendental over `ℚ`.  Clearing denominators gives a
nonzero integer `y` with `y·β` a nonzero algebraic integer; were `exp β` algebraic, so would be
`exp (y·β) = (exp β)^y`, contradicting `exp_algInt_transcendental`. -/
theorem exp_algebraic_transcendental {β : ℂ} (hβ : IsAlgebraic ℤ β) (hβ0 : β ≠ 0) :
    Transcendental ℚ (Complex.exp β) := by
  obtain ⟨y, hy0, hyint⟩ := hβ.exists_integral_multiple
  have hyβ : y • β = (y : ℂ) * β := by rw [zsmul_eq_mul]
  have hyβ0 : y • β ≠ 0 := by rw [hyβ]; exact mul_ne_zero (by exact_mod_cast hy0) hβ0
  have hT : Transcendental ℚ (Complex.exp (y • β)) := exp_algInt_transcendental hyint hyβ0
  intro hcon
  apply hT
  have hpow : Complex.exp (y • β) = (Complex.exp β) ^ y := by rw [hyβ, Complex.exp_int_mul]
  rw [hpow]
  obtain (msign | msign) := y
  · rw [Int.ofNat_eq_natCast, zpow_natCast]; exact hcon.pow msign
  · rw [zpow_negSucc]; exact IsAlgebraic.inv_iff.mpr (hcon.pow (msign + 1))


end GaloisForLFunctions.RHTower
