/-
# The weld spectrum is transcendental: prime rates `log p` are transcendental reals

A native invariant of the archimedean–difference weld `𝓜⁺`, intrinsic to how the archimedean
generator `∂_s` glues to the prime shifts `{σ_p}`.  On the difference algebra `[∂_s, σ_p] =
−(log p)·σ_p`, so the spectrum of `ad(∂_s)` is the rate group `primeLogLattice = ⟨log p⟩ ⊆ ℝ`
(`SeamSpectrumDensity`).  This file records that **every nonzero element of that spectrum is
transcendental** (`weld_spectrum_transcendental`), strictly refining the recorded density
(`primeLogLattice_dense`) and irrationality (`primeLog_irrational`).

`Mathlib` proves only the analytic half of Lindemann–Weierstrass
(`LindemannWeierstrass.exp_polynomial_approx`).  The algebraic half is supplied here by
`exp_relation_ne`: given the complete conjugate set `β₁, …, β_d` of a monic `μ ∈ ℤ[X]`, an integer
coefficient family `cf`, the expanded exponential relation `∑_S cf(|S|)·e^{σ_S} = 0`, and the
nondegeneracy `∑_{σ_S = Tr β} cf(|S|) ≠ 0`, a contradiction follows.  The mechanism is Hermite's:
shift the relation by the integer trace `Tr β`, symmetrise over the Galois orbit to a `ℤ`-integer
relation, multiply by the analytic approximant `nₚ`, and estimate with `exp_polynomial_approx` to
force a nonzero integer of absolute value `< 1`.  Two coefficient families instantiate it: the
integer-value case `cf(k) = (−M)^{d−k}` (product `∏(e^{β_j} − M)`, nondegeneracy `≡ 1 mod M`) and the
rational-value case `cf(k) = B^{k}(−A)^{d−k}` (product `∏(B·e^{β_j} − A)`, nondegeneracy `≡ B^d mod A`
with `gcd(A,B) = 1`).  Feeding algebraic integers and clearing denominators gives `log q`
transcendental for every positive rational `q ≠ 1`, hence for the whole weld spectrum.
-/

import Mathlib
import GaloisForLFunctions.HTGeometry.SymmetricConjugateIntegral
import GaloisForLFunctions.HTGeometry.WeldClassTable

open Polynomial MvPolynomial
open scoped Classical Nat
open GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.RHTower

theorem exp_relation_ne {d : ℕ} (μ : ℤ[X]) (β : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (β j)) Finset.univ.val).prod
        = μ.map (Int.castRingHom ℂ))
    (w : ℤ) (hw : (∑ j : Fin d, β j) = (w : ℂ)) (cf : ℕ → ℤ)
    (hrel : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ((cf S.card : ℤ) : ℂ) * Complex.exp (∑ j ∈ S, β j) = 0)
    (ha0 : (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => (∑ j ∈ S, β j) = (w : ℂ)), cf S.card) ≠ 0) : False := by
  set wc : ℂ := (w : ℂ) with hwc
  -- shifted relation
  have hrel2 : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      ((cf S.card : ℤ) : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc) = 0 := by
    have hstep : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        ((cf S.card : ℤ) : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc)
        = (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
            ((cf S.card : ℤ) : ℂ) * Complex.exp (∑ j ∈ S, β j)) * Complex.exp (-wc) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      rw [mul_assoc, ← Complex.exp_add]
      ring_nf
    rw [hstep, hrel, zero_mul]
  -- the ℤ[X] polynomial whose ℂ-roots are the subset sums
  obtain ⟨P, hP⟩ := subsetSum_poly_lifts μ β hβ
  have hP' : P.map (Int.castRingHom ℂ)
      = ∏ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          (Polynomial.X - Polynomial.C (∑ j ∈ S, β j)) := hP
  set fsh : ℤ[X] := P.comp (Polynomial.X + Polynomial.C w) with hfsh
  have hfshmap : fsh.map (Int.castRingHom ℂ)
      = ∏ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          (Polynomial.X - Polynomial.C ((∑ j ∈ S, β j) - wc)) := by
    rw [hfsh, Polynomial.map_comp, hP', Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
        Polynomial.prod_comp]
    refine Finset.prod_congr rfl (fun S _ => ?_)
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, hwc, Polynomial.C_sub]
    simp only [eq_intCast]
    ring
  have hfsh0 : fsh ≠ 0 := by
    intro h0
    rw [h0, Polynomial.map_zero] at hfshmap
    have hne : (∏ S ∈ (Finset.univ : Finset (Fin d)).powerset,
        (Polynomial.X - Polynomial.C ((∑ j ∈ S, β j) - wc))) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun S _ => Polynomial.X_sub_C_ne_zero _)
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
  have hroot : ∀ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      ((∑ j ∈ S, β j) - wc) ≠ 0 → ((∑ j ∈ S, β j) - wc) ∈ g.aroots ℂ := by
    intro S hS hne
    have hfr : (fsh.map (Int.castRingHom ℂ)).eval ((∑ j ∈ S, β j) - wc) = 0 := by
      rw [hfshmap, Polynomial.eval_prod]
      refine Finset.prod_eq_zero hS ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
    rw [hfactor, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at hfr
    have hgr : (g.map (Int.castRingHom ℂ)).eval ((∑ j ∈ S, β j) - wc) = 0 :=
      (mul_eq_zero.mp hfr).resolve_left (pow_ne_zero _ hne)
    rw [Polynomial.mem_aroots]
    refine ⟨hgne, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq]
    exact hgr
  set a0 : ℤ := ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => (∑ j ∈ S, β j) = wc), cf S.card with ha0def
  have hsplit : (a0 : ℂ) + ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => (∑ j ∈ S, β j) ≠ wc),
      ((cf S.card : ℤ) : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc) = 0 := by
    have he : (a0 : ℂ) = ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => (∑ j ∈ S, β j) = wc),
        ((cf S.card : ℤ) : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc) := by
      rw [ha0def]; push_cast
      refine Finset.sum_congr rfl (fun S hS => ?_)
      rw [Finset.mem_filter] at hS
      rw [hS.2, sub_self, Complex.exp_zero, mul_one]
    rw [he, Finset.sum_filter_add_sum_filter_not]
    exact hrel2
  have ha0ne : a0 ≠ 0 := ha0
  -- ============ analytic finish ============
  have hg0e : g.eval 0 ≠ 0 := by rw [← Polynomial.coeff_zero_eq_eval_zero]; exact hg0
  obtain ⟨B, hB⟩ := LindemannWeierstrass.exp_polynomial_approx g hg0e
  have hsum_exp : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => (∑ j ∈ S, β j) ≠ wc),
      ((cf S.card : ℤ) : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc) = -(a0 : ℂ) :=
    eq_neg_of_add_eq_zero_right hsplit
  set Cabs : ℝ := ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => (∑ j ∈ S, β j) ≠ wc), |((cf S.card : ℤ) : ℝ)| with hCabs
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
  set Φ : MvPolynomial (Fin d) ℤ :=
    ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
      (cf S.card) •
        Polynomial.aeval ((∑ j ∈ S, MvPolynomial.X j) - ∑ j : Fin d, MvPolynomial.X (R := ℤ) j) gp
    with hΦ
  have hΦsym : Φ.IsSymmetric := by
    intro σ
    rw [hΦ, map_sum]
    refine Finset.sum_nbij' (fun T => T.image σ) (fun T => T.image σ.symm) ?_ ?_ ?_ ?_ ?_
    · intro T _; simp
    · intro T _; simp
    · intro T _; simp [Finset.image_image]
    · intro T _; simp [Finset.image_image]
    · intro T _
      have hargeq : (MvPolynomial.rename σ)
          ((∑ j ∈ T, MvPolynomial.X j) - ∑ j : Fin d, MvPolynomial.X (R := ℤ) j)
          = (∑ j ∈ T.image σ, MvPolynomial.X j) - ∑ j : Fin d, MvPolynomial.X (R := ℤ) j := by
        rw [map_sub]
        congr 1
        · rw [map_sum, Finset.sum_image (fun a _ b _ h => σ.injective h)]
          exact Finset.sum_congr rfl (fun j _ => by simp [MvPolynomial.rename_X])
        · rw [map_sum]; simp_rw [MvPolynomial.rename_X]; exact Equiv.sum_comp σ _
      rw [map_zsmul, ← Polynomial.aeval_algHom_apply, hargeq,
          Finset.card_image_of_injective _ σ.injective]
  obtain ⟨T₀, hT₀⟩ := symmetric_aeval_conj_isInt μ β hβ Φ hΦsym
  have hΦeval : (MvPolynomial.aeval β) Φ
      = ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset,
          ((cf S.card : ℤ) : ℂ) * Polynomial.aeval ((∑ j ∈ S, β j) - wc) gp := by
    rw [hΦ, map_sum]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have hargβ : (MvPolynomial.aeval β)
        ((∑ j ∈ S, MvPolynomial.X j) - ∑ j : Fin d, MvPolynomial.X (R := ℤ) j)
        = (∑ j ∈ S, β j) - wc := by
      rw [map_sub, map_sum, map_sum]
      simp only [MvPolynomial.aeval_X]
      rw [hw]
    rw [map_zsmul, ← Polynomial.aeval_algHom_apply, hargβ, zsmul_eq_mul]
  have hev0 : Polynomial.aeval (0 : ℂ) gp = ((gp.eval 0 : ℤ) : ℂ) := by
    have h0 : ((0 : ℂ)) = (algebraMap ℤ ℂ) (0 : ℤ) := by simp
    rw [h0, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]; simp
  have hTfull : (T₀ : ℂ) = (a0 : ℂ) * ((gp.eval 0 : ℤ) : ℂ)
      + ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
          (fun S => (∑ j ∈ S, β j) ≠ wc),
          ((cf S.card : ℤ) : ℂ) * Polynomial.aeval ((∑ j ∈ S, β j) - wc) gp := by
    rw [← hT₀, hΦeval, ← Finset.sum_filter_add_sum_filter_not
        ((Finset.univ : Finset (Fin d)).powerset) (fun S => (∑ j ∈ S, β j) = wc)]
    congr 1
    rw [ha0def]; push_cast; rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    rw [Finset.mem_filter] at hS
    rw [hS.2, sub_self, hev0]
  set T : ℤ := T₀ - a0 * gp.eval 0 with hT
  have hTcast : (T : ℂ) = ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => (∑ j ∈ S, β j) ≠ wc),
      ((cf S.card : ℤ) : ℂ) * Polynomial.aeval ((∑ j ∈ S, β j) - wc) gp := by
    rw [hT]; push_cast; rw [hTfull]; ring
  have hbound : ∀ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => (∑ j ∈ S, β j) ≠ wc),
      ‖(n_p : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc)
        - (p : ℂ) * Polynomial.aeval ((∑ j ∈ S, β j) - wc) gp‖ ≤ B ^ p / (p - 1)! := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    have hr : ((∑ j ∈ S, β j) - wc) ∈ g.aroots ℂ :=
      hroot S (Finset.mem_powerset.mpr hS.1) (sub_ne_zero.mpr hS.2)
    have hb := hgp_bound hr
    rw [zsmul_eq_mul, nsmul_eq_mul] at hb
    exact hb
  set Iℤ : ℤ := a0 * n_p + (p : ℤ) * T with hIℤ
  set δfun : Finset (Fin d) → ℂ := fun S => (((cf S.card : ℤ) : ℂ))
      * ((n_p : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc)
        - (p : ℂ) * Polynomial.aeval ((∑ j ∈ S, β j) - wc) gp) with hδ
  have hkey : (Iℤ : ℂ) = - ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
      (fun S => (∑ j ∈ S, β j) ≠ wc), δfun S := by
    have expand : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => (∑ j ∈ S, β j) ≠ wc), δfun S
        = (n_p : ℂ) * (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
            (fun S => (∑ j ∈ S, β j) ≠ wc),
            ((cf S.card : ℤ) : ℂ) * Complex.exp ((∑ j ∈ S, β j) - wc))
          - (p : ℂ) * (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
            (fun S => (∑ j ∈ S, β j) ≠ wc),
            ((cf S.card : ℤ) : ℂ) * Polynomial.aeval ((∑ j ∈ S, β j) - wc) gp) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      simp only [hδ]; ring
    rw [expand, hsum_exp, ← hTcast, hIℤ]
    push_cast; ring
  have hnorm : ‖(Iℤ : ℂ)‖ < 1 := by
    rw [hkey, norm_neg]
    calc ‖∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
            (fun S => (∑ j ∈ S, β j) ≠ wc), δfun S‖
        ≤ ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
            (fun S => (∑ j ∈ S, β j) ≠ wc), ‖δfun S‖ := norm_sum_le _ _
      _ ≤ ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
            (fun S => (∑ j ∈ S, β j) ≠ wc),
            |((cf S.card : ℤ) : ℝ)| * (B ^ p / (p - 1)!) := by
          refine Finset.sum_le_sum (fun S hS => ?_)
          rw [hδ]
          simp only [norm_mul]
          gcongr
          · apply le_of_eq
            rw [Complex.norm_intCast]
          · exact hbound S hS
      _ = Cabs * (B ^ p / (p - 1)!) := by rw [hCabs, ← Finset.sum_mul]
      _ < 1 := hP₀ p hp_ge_P₀
  have hI0 : Iℤ = 0 := by
    have habs : |(Iℤ : ℝ)| < 1 := by rw [← Complex.norm_intCast]; exact hnorm
    exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast habs)
  have hdvd : (p : ℤ) ∣ a0 * n_p := by
    have heq : a0 * n_p = -((p : ℤ) * T) := by
      have := hI0; rw [hIℤ] at this; linarith
    rw [heq]; exact (Dvd.intro T rfl).neg_right
  have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
  rcases hp_prime_int.dvd_mul.mp hdvd with h | h
  · have hdvdnat : p ∣ a0.natAbs := by
      have := Int.natAbs_dvd_natAbs.mpr h; rwa [Int.natAbs_natCast] at this
    have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr ha0ne) hdvdnat
    exact absurd hle (not_le.mpr hp_gt_a0)
  · exact hnp_ndvd h

theorem exp_conj_ne {d : ℕ} (μ : ℤ[X]) (β : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (β j)) Finset.univ.val).prod
        = μ.map (Int.castRingHom ℂ))
    (M : ℤ) (hM : 2 ≤ M) (j₀ : Fin d) (hrel : Complex.exp (β j₀) = (M : ℂ)) : False := by
  obtain ⟨w, hw⟩ := symmetric_aeval_conj_isInt μ β hβ (MvPolynomial.esymm (Fin d) ℤ 1)
    (MvPolynomial.esymm_isSymmetric _ _ _)
  rw [MvPolynomial.esymm_one, map_sum] at hw
  simp only [MvPolynomial.aeval_X] at hw
  refine exp_relation_ne μ β hβ w hw (fun k => (-M : ℤ) ^ (d - k)) ?_ ?_
  · have hkey : ∏ j : Fin d, (Complex.exp (β j) + (-M : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hrel]; ring)
    rw [Finset.prod_add] at hkey
    rw [← hkey]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Complex.exp_sum, Finset.prod_const]
    have hcard : (Finset.univ \ S).card = d - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [hcard]; push_cast; ring
  · show (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => (∑ j ∈ S, β j) = (w : ℂ)), (-M : ℤ) ^ (d - S.card)) ≠ 0
    have hunivmem : (Finset.univ : Finset (Fin d)) ∈
        (Finset.univ : Finset (Fin d)).powerset.filter (fun S => (∑ j ∈ S, β j) = (w : ℂ)) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, by simpa using hw⟩
    have ha0M : ∃ K : ℤ, (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => (∑ j ∈ S, β j) = (w : ℂ)), (-M : ℤ) ^ (d - S.card)) = 1 + M * K := by
      have hdvd : M ∣ ∑ S ∈ ((Finset.univ : Finset (Fin d)).powerset.filter
          (fun S => (∑ j ∈ S, β j) = (w : ℂ))).erase Finset.univ, (-M : ℤ) ^ (d - S.card) := by
        refine Finset.dvd_sum (fun S hS => ?_)
        have hSne : S ≠ Finset.univ := (Finset.mem_erase.mp hS).1
        have hScard : S.card < d := by
          have := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hSne⟩)
          simpa [Finset.card_univ, Fintype.card_fin] using this
        have hexp : d - S.card ≠ 0 := by omega
        exact dvd_trans (dvd_neg.mpr (dvd_refl M)) (dvd_pow_self (-M) hexp)
      obtain ⟨K, hK⟩ := hdvd
      refine ⟨K, ?_⟩
      have hae := (Finset.add_sum_erase _ (fun S => (-M : ℤ) ^ (d - S.card)) hunivmem).symm
      rw [hae, hK, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero]
    obtain ⟨K, hKeq⟩ := ha0M
    rw [hKeq]
    intro h0
    have hdvd1 : M ∣ 1 := ⟨-K, by rw [mul_neg]; linarith⟩
    have hle := Int.le_of_dvd (by norm_num) hdvd1
    omega

theorem exp_conj_ne_rat {d : ℕ} (μ : ℤ[X]) (β : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (β j)) Finset.univ.val).prod
        = μ.map (Int.castRingHom ℂ))
    (A B : ℤ) (hA : 2 ≤ A) (hcop : IsCoprime A B) (j₀ : Fin d)
    (hrel : (B : ℂ) * Complex.exp (β j₀) = (A : ℂ)) : False := by
  obtain ⟨w, hw⟩ := symmetric_aeval_conj_isInt μ β hβ (MvPolynomial.esymm (Fin d) ℤ 1)
    (MvPolynomial.esymm_isSymmetric _ _ _)
  rw [MvPolynomial.esymm_one, map_sum] at hw
  simp only [MvPolynomial.aeval_X] at hw
  refine exp_relation_ne μ β hβ w hw (fun k => B ^ k * (-A) ^ (d - k)) ?_ ?_
  · have hkey : ∏ j : Fin d, ((B : ℂ) * Complex.exp (β j) + (-A : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j₀) (by rw [hrel]; ring)
    rw [Finset.prod_add] at hkey
    rw [← hkey]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have hcard : (Finset.univ \ S).card = d - S.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Complex.exp_sum, hcard]
    push_cast; ring
  · show (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => (∑ j ∈ S, β j) = (w : ℂ)), B ^ S.card * (-A) ^ (d - S.card)) ≠ 0
    have hunivmem : (Finset.univ : Finset (Fin d)) ∈
        (Finset.univ : Finset (Fin d)).powerset.filter (fun S => (∑ j ∈ S, β j) = (w : ℂ)) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_univ _, by simpa using hw⟩
    have hsumeq : ∃ K : ℤ, (∑ S ∈ (Finset.univ : Finset (Fin d)).powerset.filter
        (fun S => (∑ j ∈ S, β j) = (w : ℂ)), B ^ S.card * (-A) ^ (d - S.card)) = B ^ d + A * K := by
      have hdvd : A ∣ ∑ S ∈ ((Finset.univ : Finset (Fin d)).powerset.filter
          (fun S => (∑ j ∈ S, β j) = (w : ℂ))).erase Finset.univ,
          B ^ S.card * (-A) ^ (d - S.card) := by
        refine Finset.dvd_sum (fun S hS => ?_)
        have hSne : S ≠ Finset.univ := (Finset.mem_erase.mp hS).1
        have hScard : S.card < d := by
          have := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hSne⟩)
          simpa [Finset.card_univ, Fintype.card_fin] using this
        have hexp : d - S.card ≠ 0 := by omega
        exact (dvd_trans (dvd_neg.mpr (dvd_refl A)) (dvd_pow_self (-A) hexp)).mul_left (B ^ S.card)
      obtain ⟨K, hK⟩ := hdvd
      refine ⟨K, ?_⟩
      have hae := (Finset.add_sum_erase _ (fun S => B ^ S.card * (-A : ℤ) ^ (d - S.card))
        hunivmem).symm
      rw [hae, hK, Finset.card_univ, Fintype.card_fin, Nat.sub_self, pow_zero, mul_one]
    obtain ⟨K, hKeq⟩ := hsumeq
    rw [hKeq]
    intro h0
    have hAdvd : A ∣ B ^ d := ⟨-K, by rw [mul_neg]; linarith⟩
    have hu : IsUnit A := hcop.pow_right.isUnit_of_dvd' (dvd_refl A) hAdvd
    rw [Int.isUnit_iff] at hu
    omega

theorem exp_algInt_ne_rat (β : ℂ) (hβint : IsIntegral ℤ β) (A B : ℤ) (hA : 2 ≤ A)
    (hcop : IsCoprime A B) (hrel : (B : ℂ) * Complex.exp β = (A : ℂ)) : False := by
  have hμmonic : (minpoly ℤ β).Monic := minpoly.monic hβint
  have hqmonic : ((minpoly ℤ β).map (Int.castRingHom ℂ)).Monic := hμmonic.map _
  have hqdeg : ((minpoly ℤ β).map (Int.castRingHom ℂ)).natDegree = (minpoly ℤ β).natDegree :=
    Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℂ)) _
  have hcard : Multiset.card ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots
      = (minpoly ℤ β).natDegree := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), hqdeg]
  obtain ⟨l, hl⟩ := Quotient.exists_rep ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots
  have hmap : Multiset.map l.get Finset.univ.val
      = ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots := by
    rw [Fin.univ_val_map, List.ofFn_get]; exact hl
  have hβprod : (Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val).prod
      = (minpoly ℤ β).map (Int.castRingHom ℂ) := by
    have hrw : (Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val)
        = ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.map (fun a => Polynomial.X - Polynomial.C a) := by
      rw [← hmap, Multiset.map_map]; rfl
    rw [hrw, prod_multiset_X_sub_C_of_monic_of_roots_card_eq hqmonic (hcard.trans hqdeg.symm)]
  have hβroot : β ∈ ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots := by
    rw [Polynomial.mem_roots']
    refine ⟨hqmonic.ne_zero, ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    have hh := minpoly.aeval ℤ β
    rw [Polynomial.aeval_def] at hh
    exact hh
  have hβmem : β ∈ Multiset.map l.get Finset.univ.val := by rw [hmap]; exact hβroot
  obtain ⟨j₀, _, hj₀⟩ := Multiset.mem_map.mp hβmem
  exact exp_conj_ne_rat (d := l.length) (minpoly ℤ β) l.get hβprod A B hA hcop j₀
    (by rw [hj₀]; exact hrel)

/-- **`log r` is transcendental for a rational `r > 1`.**  Clearing denominators makes `N·log r` an
algebraic integer `β` with `B·exp β = A`, `A = r.num^N ≥ 2`, `B = r.den^N`, `gcd(A,B) = 1`;
`exp_algInt_ne_rat` yields a contradiction. -/
theorem transcendental_log_rat_gt {r : ℚ} (hr : 1 < r) : Transcendental ℚ (Real.log r) := by
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by linarith : (0 : ℚ) < r)
  have hnum : 2 ≤ r.num := by
    have hdR : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.den_pos
    have hbase : (r.den : ℝ) * (r : ℝ) = (r.num : ℝ) := by rw [Rat.cast_def]; field_simp
    have hlt : (r.den : ℝ) < (r.num : ℝ) := by
      calc (r.den : ℝ) = (r.den : ℝ) * 1 := by ring
        _ < (r.den : ℝ) * (r : ℝ) := by apply mul_lt_mul_of_pos_left _ hdR; exact_mod_cast hr
        _ = (r.num : ℝ) := hbase
    have hden1 : 1 ≤ r.den := r.den_pos
    have : (r.den : ℤ) < r.num := by exact_mod_cast hlt
    omega
  have hcopnd : IsCoprime r.num ((r.den : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast r.reduced
  have hZ : Transcendental ℤ (Real.log r) := by
    intro halg
    obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
    have hcint : IsIntegral ℤ ((y.natAbs : ℤ) • Real.log r) := by
      have hz : ((y.natAbs : ℤ) • Real.log r) = |y| • Real.log r := by rw [Int.abs_eq_natAbs]
      rw [hz]; rcases abs_choice y with h | h <;> rw [h]
      · exact hyint
      · rw [neg_smul]; exact hyint.neg
    set N := y.natAbs with hN
    have hN0 : N ≠ 0 := Int.natAbs_ne_zero.mpr hy0
    have hβℝint : IsIntegral ℤ ((N : ℝ) * Real.log r) := by
      have hz : ((N : ℤ) • Real.log r) = (N : ℝ) * Real.log r := by
        rw [zsmul_eq_mul]; push_cast; ring
      rwa [hz] at hcint
    have hβℂint : IsIntegral ℤ ((algebraMap ℝ ℂ) ((N : ℝ) * Real.log r)) :=
      hβℝint.map (IsScalarTower.toAlgHom ℤ ℝ ℂ)
    set β : ℂ := (N : ℂ) * ((Real.log r : ℝ) : ℂ) with hβ
    have hβeq : (algebraMap ℝ ℂ) ((N : ℝ) * Real.log r) = β := by
      rw [hβ]; push_cast [Complex.coe_algebraMap]; ring
    rw [hβeq] at hβℂint
    have hexpN : Complex.exp β = (r : ℂ) ^ N := by
      rw [hβ, Complex.exp_nat_mul,
        show Complex.exp ((Real.log r : ℝ) : ℂ) = (r : ℂ) from by
          rw [← Complex.ofReal_exp, Real.exp_log hr0]; push_cast; ring]
    have hAge : 2 ≤ r.num ^ N := le_trans hnum (le_self_pow₀ (by omega) hN0)
    have hcop : IsCoprime (r.num ^ N) ((r.den : ℤ) ^ N) := hcopnd.pow
    have hBrel : (((r.den : ℤ) ^ N : ℤ) : ℂ) * Complex.exp β = ((r.num ^ N : ℤ) : ℂ) := by
      rw [hexpN]; push_cast; rw [← mul_pow]
      congr 1
      have hd : ((r.den : ℤ) : ℂ) ≠ 0 := by exact_mod_cast r.den_nz
      rw [Rat.cast_def]; field_simp
    exact exp_algInt_ne_rat β hβℂint (r.num ^ N) ((r.den : ℤ) ^ N) hAge hcop hBrel
  exact fun hq => hZ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hq)

/-- **Every nonzero rate of the weld spectrum is transcendental.**  For a positive rational `r ≠ 1`,
`log r` is transcendental.  Since `primeLogLattice = ⟨log p⟩ = {log r : r ∈ ℚ_{>0}}`, this says every
nonzero element of the `ad(∂_s)`-spectrum is a transcendental real — the full native
spectral-transcendence invariant of the weld, blind to any zero. -/
theorem transcendental_log_rat {r : ℚ} (hr0 : 0 < r) (hr1 : r ≠ 1) :
    Transcendental ℚ (Real.log r) := by
  rcases lt_or_gt_of_ne hr1 with hlt | hgt
  · have h1 : 1 < 1 / r := by rw [lt_div_iff₀ hr0]; linarith
    have hlog : Real.log ((1 / r : ℚ) : ℝ) = -Real.log (r : ℝ) := by
      push_cast; rw [one_div, Real.log_inv]
    have hT := transcendental_log_rat_gt h1
    rw [hlog] at hT
    exact fun h => hT h.neg
  · exact transcendental_log_rat_gt hgt


/-- **The exponential of a nonzero algebraic integer is never a rational integer `≥ 2`.**  If `β` is
integral over `ℤ` and `exp β = M` for an integer `M ≥ 2`, a contradiction follows.  The minimal
polynomial `minpoly ℤ β` is monic over `ℤ`; its complex roots form the conjugate set to which
`exp_conj_ne` applies, with `β` itself the distinguished root carrying the exponential relation. -/
theorem exp_algInt_ne (β : ℂ) (hβint : IsIntegral ℤ β) (M : ℤ) (hM : 2 ≤ M)
    (hrel : Complex.exp β = (M : ℂ)) : False := by
  have hμmonic : (minpoly ℤ β).Monic := minpoly.monic hβint
  have hqmonic : ((minpoly ℤ β).map (Int.castRingHom ℂ)).Monic := hμmonic.map _
  have hqdeg : ((minpoly ℤ β).map (Int.castRingHom ℂ)).natDegree = (minpoly ℤ β).natDegree :=
    Polynomial.natDegree_map_eq_of_injective (Int.cast_injective (α := ℂ)) _
  have hcard : Multiset.card ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots
      = (minpoly ℤ β).natDegree := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), hqdeg]
  obtain ⟨l, hl⟩ := Quotient.exists_rep ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots
  have hmap : Multiset.map l.get Finset.univ.val
      = ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots := by
    rw [Fin.univ_val_map, List.ofFn_get]; exact hl
  have hβprod : (Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val).prod
      = (minpoly ℤ β).map (Int.castRingHom ℂ) := by
    have hrw : (Multiset.map (fun j => Polynomial.X - Polynomial.C (l.get j)) Finset.univ.val)
        = ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots.map (fun a => Polynomial.X - Polynomial.C a) := by
      rw [← hmap, Multiset.map_map]; rfl
    rw [hrw, prod_multiset_X_sub_C_of_monic_of_roots_card_eq hqmonic (hcard.trans hqdeg.symm)]
  have hβroot : β ∈ ((minpoly ℤ β).map (Int.castRingHom ℂ)).roots := by
    rw [Polynomial.mem_roots']
    refine ⟨hqmonic.ne_zero, ?_⟩
    rw [Polynomial.IsRoot.def, Polynomial.eval_map]
    have hh := minpoly.aeval ℤ β
    rw [Polynomial.aeval_def] at hh
    exact hh
  have hβmem : β ∈ Multiset.map l.get Finset.univ.val := by rw [hmap]; exact hβroot
  obtain ⟨j₀, _, hj₀⟩ := Multiset.mem_map.mp hβmem
  exact exp_conj_ne (d := l.length) (minpoly ℤ β) l.get hβprod M hM j₀ (by rw [hj₀]; exact hrel)

/-- **`log n` is transcendental for every integer `n ≥ 2`.**  Were `log n` algebraic, some positive
integer multiple `a·log n` would be an algebraic integer `β` with `exp β = n^a ≥ 2`, contradicting
`exp_algInt_ne`.  This is the archimedean rate `log n` — an element of the weld spectrum
`primeLogLattice` — refined from irrational (`primeLog_irrational`) to transcendental. -/
theorem transcendental_log_nat {n : ℕ} (hn : 2 ≤ n) : Transcendental ℚ (Real.log n) := by
  have hn0 : 0 < n := by omega
  have hZ : Transcendental ℤ (Real.log n) := by
    intro halg
    obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
    have hcint : IsIntegral ℤ ((y.natAbs : ℤ) • Real.log n) := by
      have hz : ((y.natAbs : ℤ) • Real.log n) = |y| • Real.log n := by rw [Int.abs_eq_natAbs]
      rw [hz]
      rcases abs_choice y with h | h <;> rw [h]
      · exact hyint
      · rw [neg_smul]; exact hyint.neg
    set a := y.natAbs with ha
    have ha0 : a ≠ 0 := Int.natAbs_ne_zero.mpr hy0
    have hMn : 2 ≤ n ^ a := le_trans hn (Nat.le_self_pow ha0 n)
    have hβℝint : IsIntegral ℤ ((a : ℝ) * Real.log n) := by
      have hz : ((a : ℤ) • Real.log n) = (a : ℝ) * Real.log n := by
        rw [zsmul_eq_mul]; push_cast; ring
      rwa [hz] at hcint
    have hβℂint : IsIntegral ℤ ((algebraMap ℝ ℂ) ((a : ℝ) * Real.log n)) :=
      hβℝint.map (IsScalarTower.toAlgHom ℤ ℝ ℂ)
    set β : ℂ := (a : ℂ) * ((Real.log n : ℝ) : ℂ) with hβ
    have hβeq : (algebraMap ℝ ℂ) ((a : ℝ) * Real.log n) = β := by
      rw [hβ]; push_cast [Complex.coe_algebraMap]; ring
    rw [hβeq] at hβℂint
    have hexp : Complex.exp β = ((n ^ a : ℕ) : ℂ) := by
      rw [hβ, Complex.exp_nat_mul,
        show Complex.exp ((Real.log n : ℝ) : ℂ) = (n : ℂ) from by
          rw [← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hn0)]; norm_cast]
      push_cast; ring
    exact exp_algInt_ne β hβℂint ((n ^ a : ℕ) : ℤ) (by exact_mod_cast hMn)
      (by rw [hexp]; push_cast; ring)
  exact fun hq => hZ ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hq)

/-- **Every prime rate of the weld spectrum is transcendental.**  The generator `log p` of the
`ad(∂_s)`-spectrum `primeLogLattice` attached to the prime shift `σ_p` is a transcendental real. -/
theorem primeLog_transcendental {p : ℕ} (hp : p.Prime) : Transcendental ℚ (Real.log p) :=
  transcendental_log_nat hp.two_le

/-- **The integer rungs of the weld spectrum are transcendental.**  For every `n ≥ 2`, the rate
`log n` lies in the spectrum `primeLogLattice` of `ad(∂_s)` and is transcendental — a native
spectral-transcendence invariant of the archimedean–difference weld, strictly finer than the
gaplessness (`primeLogLattice_dense`) and irrationality (`primeLog_irrational`) already recorded, and
blind to the location of any zero. -/
theorem weld_spectrum_rate_transcendental {n : ℕ} (hn : 2 ≤ n) :
    Real.log (n : ℕ) ∈ primeLogLattice ∧ Transcendental ℚ (Real.log n) :=
  ⟨log_nat_mem_primeLogLattice n (by omega), transcendental_log_nat hn⟩

/-- **The weld spectrum is transcendental.**  Every nonzero element of `primeLogLattice`, the
`ad(∂_s)`-spectrum of the archimedean–difference weld, is a transcendental real.  Since the spectrum
is `⟨log p⟩ = {log q : q ∈ ℚ_{>0}}`, this is the complete native spectral-transcendence invariant:
the weld's rate group meets the algebraic numbers only at `0`.  It strictly refines the recorded
gaplessness (`primeLogLattice_dense`) and irrationality (`primeLog_irrational`), and is blind to the
location of any zero. -/
theorem weld_spectrum_transcendental (x : ℝ) (hx : x ∈ primeLogLattice) (hx0 : x ≠ 0) :
    Transcendental ℚ x := by
  have hlog : ∃ q : ℚ, 0 < q ∧ x = Real.log (q : ℝ) := by
    refine AddSubgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro y ⟨p, hp, rfl⟩
      exact ⟨(p : ℚ), by exact_mod_cast hp.pos, by norm_cast⟩
    · exact ⟨1, one_pos, by rw [Rat.cast_one, Real.log_one]⟩
    · rintro a b _ _ ⟨qa, hqa, rfl⟩ ⟨qb, hqb, rfl⟩
      exact ⟨qa * qb, mul_pos hqa hqb, by
        rw [Rat.cast_mul, Real.log_mul (by positivity) (by positivity)]⟩
    · rintro a _ ⟨qa, hqa, rfl⟩
      exact ⟨qa⁻¹, by positivity, by rw [Rat.cast_inv, Real.log_inv]⟩
  obtain ⟨q, hq0, rfl⟩ := hlog
  have hq1 : q ≠ 1 := by
    intro h; rw [h, Rat.cast_one, Real.log_one] at hx0; exact hx0 rfl
  exact transcendental_log_rat hq0 hq1

end GaloisForLFunctions.RHTower
