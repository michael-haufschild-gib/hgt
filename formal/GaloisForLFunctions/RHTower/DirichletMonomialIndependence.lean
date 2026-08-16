import Mathlib

/-!
# Dirichlet monomials are linearly independent

The functions `s ↦ n^{-s}`, one for each positive integer `n`, are linearly independent over `ℂ`.
Equivalently: a Dirichlet polynomial that vanishes identically has all coefficients zero.

The proof is the standard smallest-modulus argument.  If a finite Dirichlet polynomial vanishes,
let `n₀` be the smallest modulus carrying a nonzero coefficient; multiplying by `n₀^t` and letting
the real exponent `t` tend to infinity kills every larger modulus and leaves the coefficient at
`n₀`.  Only real exponents are used, so the hypothesis is as weak as possible.

This is the "triviality lemma" for Dirichlet-polynomial auxiliaries: no nontrivial finite
combination of `{n^{-s}}` is the zero function.

## Main results

* `coeff_eq_zero_of_dirichletSum_eq_zero` — vanishing on the reals forces all coefficients zero;
* `linearIndependent_dirichletMonomial` — the family `n ↦ (s ↦ n^{-s})` is linearly independent.
-/

noncomputable section

namespace RHTower

open Filter Topology

/-- **The triviality lemma for Dirichlet polynomials.**  If a finite combination of the Dirichlet
monomials `n^{-t}` vanishes for every real exponent, every coefficient vanishes. -/
theorem coeff_eq_zero_of_dirichletSum_eq_zero
    {S : Finset ℕ} (hS : ∀ n ∈ S, 0 < n) (f : ℕ → ℂ)
    (h : ∀ t : ℝ, ∑ n ∈ S, f n * (((n : ℝ) ^ (-t) : ℝ) : ℂ) = 0) :
    ∀ n ∈ S, f n = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨m, hmS, hm⟩ := hcon
  set T : Finset ℕ := S.filter (fun n => f n ≠ 0) with hT
  have hTne : T.Nonempty := ⟨m, by simp [hT, hmS, hm]⟩
  have hTS : T ⊆ S := Finset.filter_subset _ _
  set n₀ : ℕ := T.min' hTne with hn₀
  have hn₀T : n₀ ∈ T := T.min'_mem hTne
  have hn₀S : n₀ ∈ S := hTS hn₀T
  have hn₀pos : 0 < n₀ := hS _ hn₀S
  have hn₀R : (0 : ℝ) < (n₀ : ℝ) := by exact_mod_cast hn₀pos
  -- restrict the sum to the support
  have hTsum : ∀ t : ℝ, ∑ n ∈ T, f n * (((n : ℝ) ^ (-t) : ℝ) : ℂ) = 0 := by
    intro t
    refine (Finset.sum_subset hTS ?_).trans (h t)
    intro n hnS hnT
    have hfn : f n = 0 := by
      by_contra hfn
      exact hnT (Finset.mem_filter.mpr ⟨hnS, hfn⟩)
    rw [hfn, zero_mul]
  -- rescale by `n₀ ^ t`
  have hscaled : ∀ t : ℝ,
      ∑ n ∈ T, f n * ((((n₀ : ℝ) / (n : ℝ)) ^ t : ℝ) : ℂ) = 0 := by
    intro t
    have hmul := congrArg (fun z : ℂ => (((n₀ : ℝ) ^ t : ℝ) : ℂ) * z) (hTsum t)
    simp only [mul_zero, Finset.mul_sum] at hmul
    rw [← hmul]
    refine Finset.sum_congr rfl (fun n hnT => ?_)
    have hnpos : 0 < n := hS _ (hTS hnT)
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    have hdiv : (((n₀ : ℝ) / (n : ℝ)) ^ t : ℝ)
        = ((n₀ : ℝ) ^ t) * ((n : ℝ) ^ (-t)) := by
      rw [Real.div_rpow hn₀R.le hnR.le, Real.rpow_neg hnR.le, div_eq_mul_inv]
    rw [hdiv]
    push_cast
    ring
  -- the rescaled sum tends to the smallest coefficient
  have hlim : Tendsto
      (fun t : ℝ => ∑ n ∈ T, f n * ((((n₀ : ℝ) / (n : ℝ)) ^ t : ℝ) : ℂ)) atTop (𝓝 (f n₀)) := by
    have hterm : ∀ n ∈ T,
        Tendsto (fun t : ℝ => f n * ((((n₀ : ℝ) / (n : ℝ)) ^ t : ℝ) : ℂ)) atTop
          (𝓝 (if n = n₀ then f n₀ else 0)) := by
      intro n hnT
      by_cases hn : n = n₀
      · rw [if_pos hn, hn]
        have hone : ∀ t : ℝ, f n₀ * ((((n₀ : ℝ) / (n₀ : ℝ)) ^ t : ℝ) : ℂ) = f n₀ := by
          intro t
          rw [div_self (ne_of_gt hn₀R), Real.one_rpow]
          simp
        simp only [hone]
        exact tendsto_const_nhds
      · rw [if_neg hn]
        have hlt : n₀ < n := lt_of_le_of_ne (T.min'_le n hnT) (Ne.symm hn)
        have hnR : (0 : ℝ) < (n : ℝ) := by
          exact_mod_cast lt_trans hn₀pos hlt
        have hb₁ : (n₀ : ℝ) / (n : ℝ) < 1 := by
          rw [div_lt_one hnR]
          exact_mod_cast hlt
        have hb₀ : (-1 : ℝ) < (n₀ : ℝ) / (n : ℝ) :=
          lt_of_lt_of_le (by norm_num) (le_of_lt (div_pos hn₀R hnR))
        have hbase := tendsto_rpow_atTop_of_base_lt_one _ hb₀ hb₁
        have hcast : Tendsto (fun t : ℝ => ((((n₀ : ℝ) / (n : ℝ)) ^ t : ℝ) : ℂ)) atTop (𝓝 0) := by
          have := (Complex.continuous_ofReal.tendsto 0).comp hbase
          simpa [Function.comp_def] using this
        simpa using hcast.const_mul (f n)
    have := tendsto_finsetSum T hterm
    simpa [Finset.sum_ite_eq' T n₀ (fun _ => f n₀), hn₀T] using this
  have : f n₀ = 0 := by
    have hconst : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 (f n₀)) := by
      simpa [hscaled] using hlim
    exact tendsto_nhds_unique hconst tendsto_const_nhds
  have : f n₀ ≠ 0 := by
    have := Finset.mem_filter.mp (hT ▸ hn₀T)
    exact this.2
  exact this ‹f n₀ = 0›

/-- **Dirichlet monomials are linearly independent.**  No nontrivial finite complex combination of
the functions `s ↦ n^{-s}`, `n` a positive integer, is the zero function. -/
theorem linearIndependent_dirichletMonomial :
    LinearIndependent ℂ
      (fun n : {n : ℕ // 0 < n} => (fun s : ℂ => (n.1 : ℂ) ^ (-s))) := by
  classical
  rw [linearIndependent_iff']
  intro S g hg i hi
  -- transport the relation to a relation over the underlying moduli
  set T : Finset ℕ := S.image (fun n : {n : ℕ // 0 < n} => n.1) with hTdef
  have hinj : Set.InjOn (fun n : {n : ℕ // 0 < n} => n.1) S := fun a _ b _ hab => Subtype.ext hab
  have hTpos : ∀ n ∈ T, 0 < n := by
    intro n hn
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hn
    exact j.2
  set f : ℕ → ℂ := fun n => if h : ∃ j ∈ S, j.1 = n then g h.choose else 0 with hfdef
  have hf : ∀ j ∈ S, f j.1 = g j := by
    intro j hj
    have hex : ∃ k ∈ S, k.1 = j.1 := ⟨j, hj, rfl⟩
    rw [hfdef]
    simp only [dif_pos hex]
    have hspec := hex.choose_spec
    have : hex.choose = j := hinj hspec.1 hj hspec.2
    rw [this]
  have hzero : ∀ t : ℝ, ∑ n ∈ T, f n * (((n : ℝ) ^ (-t) : ℝ) : ℂ) = 0 := by
    intro t
    rw [hTdef, Finset.sum_image (fun a ha b hb hab => hinj ha hb hab)]
    have := congrFun hg ((t : ℂ))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hf j hj]
    congr 1
    have hjR : (0 : ℝ) ≤ (j.1 : ℝ) := by positivity
    rw [Complex.ofReal_cpow hjR]
    push_cast
    ring_nf
  have := coeff_eq_zero_of_dirichletSum_eq_zero hTpos f hzero i.1
    (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rwa [hf i hi] at this

end RHTower
