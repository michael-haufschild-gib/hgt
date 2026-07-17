import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Critical derivative of the Suzuki coupled summatory error

For `ω > 0` the shifted Jordan--Euler coefficient `c_ω(n) = n^ω ∏_{p ∣ n} (1 - p^{-2ω})` has
Dirichlet series `ζ(s - ω) / ζ(s + ω)`.  Its summatory error against the main term
`M_ω(X) = X^{1+ω} / ((1+ω) ζ(1+2ω))` is the coupled arithmetic source of Suzuki's boundary
program.  This module proves unconditionally that the right derivative of the coupled error at
the critical exponent `ω = 0` is exactly `2 (ψ(X) - X)`: the infinitesimal Euler leakage is the
Chebyshev error, with the explicit coefficient law `∂_ω c_ω(n)|₀ = 2 Λ(n)`.
-/

open scoped ArithmeticFunction BigOperators
open Finset Filter Topology Real

noncomputable section

/-- The shifted Jordan--Euler coefficient `c_ω(n) = n^ω ∏_{p ∣ n} (1 - p^{-2ω})`. -/
noncomputable def suzukiShiftedCoefficient (ω : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ ω * ∏ p ∈ n.primeFactors, (1 - (p : ℝ) ^ (-2 * ω))

/-- The summatory function `A_ω(X) = ∑_{n ≤ X} c_ω(n)`. -/
noncomputable def suzukiShiftedSummatory (ω : ℝ) (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X, suzukiShiftedCoefficient ω n

/-- The main term `M_ω(X) = X^{1+ω} / ((1+ω) ζ(1+2ω))`.  The zeta value at the real argument
`1 + 2ω` is real, so it is recorded through its real part. -/
noncomputable def suzukiMainTerm (ω : ℝ) (X : ℕ) : ℝ :=
  (X : ℝ) ^ (1 + ω) / ((1 + ω) * (riemannZeta (((1 + 2 * ω : ℝ) : ℂ))).re)

/-- The coupled summatory error `E_ω(X) = A_ω(X) - M_ω(X)`. -/
noncomputable def suzukiCoupledError (ω : ℝ) (X : ℕ) : ℝ :=
  suzukiShiftedSummatory ω X - suzukiMainTerm ω X

private theorem hasDerivAt_one_sub_rpow_neg_two {p : ℕ} (hp : 1 ≤ p) :
    HasDerivAt (fun ω : ℝ => 1 - (p : ℝ) ^ (-2 * ω)) (2 * Real.log p) 0 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : HasDerivAt (fun ω : ℝ => Real.log p * (-2 * ω)) (Real.log p * -2) 0 := by
    have hrw : (fun ω : ℝ => Real.log p * (-2 * ω)) = fun ω => (Real.log p * -2) * ω := by
      funext ω
      ring
    rw [hrw]
    exact hasDerivAt_const_mul _
  have h2 := h1.exp
  have h3 : HasDerivAt (fun ω : ℝ => (p : ℝ) ^ (-2 * ω)) (Real.log p * -2) 0 := by
    have hrw : (fun ω : ℝ => (p : ℝ) ^ (-2 * ω)) =
        fun ω => Real.exp (Real.log p * (-2 * ω)) := by
      funext ω
      rw [Real.rpow_def_of_pos hp0]
    rw [hrw]
    simpa using h2
  have h4 := h3.const_sub 1
  have hder : (-(Real.log p * -2)) = 2 * Real.log p := by ring
  rwa [hder] at h4

private theorem hasDerivAt_finset_prod {u : Finset ℕ} {f : ℕ → ℝ → ℝ} {f' : ℕ → ℝ}
    (hf : ∀ i ∈ u, HasDerivAt (f i) (f' i) 0) :
    HasDerivAt (fun ω => ∏ i ∈ u, f i ω)
      (∑ i ∈ u, (∏ j ∈ u.erase i, f j 0) * f' i) 0 := by
  induction u using Finset.induction with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      exact hasDerivAt_const 0 1
  | @insert a u ha ihu =>
      have hfu : ∀ i ∈ u, HasDerivAt (f i) (f' i) 0 :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hfa := hf a (Finset.mem_insert_self a u)
      have hmul := hfa.mul (ihu hfu)
      simp only [Finset.prod_insert ha, Finset.sum_insert ha, Finset.erase_insert ha]
      have hterm : ∀ i ∈ u, (∏ j ∈ (insert a u).erase i, f j 0) * f' i =
          f a 0 * ((∏ j ∈ u.erase i, f j 0) * f' i) := by
        intro i hi
        have hia : a ≠ i := fun h => ha (h ▸ hi)
        rw [Finset.erase_insert_of_ne hia, Finset.prod_insert (Finset.not_mem_erase a u)]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        mul_comm ((∏ j ∈ u, f j 0)) (f' a)]
      exact hmul

/-- **Critical coefficient law.**  The derivative of the shifted Jordan--Euler coefficient at
`ω = 0` is exactly twice the von Mangoldt function: the infinitesimal Euler factor vanishes
except on prime powers, where it releases `2 log p`. -/
theorem hasDerivAt_suzukiShiftedCoefficient {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (fun ω => suzukiShiftedCoefficient ω n) (2 * Λ n) 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set P := n.primeFactors with hP
  have hfactor : ∀ p ∈ P, HasDerivAt (fun ω : ℝ => 1 - (p : ℝ) ^ (-2 * ω))
      (2 * Real.log p) 0 :=
    fun p hp => hasDerivAt_one_sub_rpow_neg_two
      (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp))
  have hprod := hasDerivAt_finset_prod hfactor
  have hbase : HasDerivAt (fun ω : ℝ => (n : ℝ) ^ ω) (Real.log n) 0 := by
    have hrw : (fun ω : ℝ => (n : ℝ) ^ ω) = fun ω => Real.exp (Real.log n * ω) := by
      funext ω
      rw [Real.rpow_def_of_pos hn0]
    rw [hrw]
    have h := (hasDerivAt_const_mul (Real.log n) (x := (0 : ℝ))).exp
    convert h using 2
    simp
  have hmul := hbase.mul hprod
  have hf0 : ∀ q : ℕ, (1 : ℝ) - (q : ℝ) ^ (-2 * (0 : ℝ)) = 0 := by
    intro q
    rw [neg_zero, Real.rpow_zero]
    norm_num
  rcases Nat.eq_zero_or_pos P.card with hcard | hcard
  · have hPempty : P = ∅ := Finset.card_eq_zero.mp hcard
    have hn1 : n = 1 := by
      by_contra h
      have hne : P.Nonempty :=
        Nat.nonempty_primeFactors.mpr (lt_of_le_of_ne hn (Ne.symm h))
      rw [hPempty] at hne
      exact Finset.not_nonempty_empty hne
    subst hn1
    convert hmul using 2
    simp [hP, hPempty]
  · have hprod0 : (∏ p ∈ P, (1 - (p : ℝ) ^ (-2 * (0 : ℝ)))) = 0 := by
      obtain ⟨p, hp⟩ := Finset.card_pos.mp hcard
      exact Finset.prod_eq_zero hp (hf0 p)
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hcard) with h1 | h2
    · obtain ⟨p, hpP⟩ := Finset.card_eq_one.mp h1
      have hD : (∑ q ∈ P, (∏ j ∈ P.erase q, (1 - (j : ℝ) ^ (-2 * (0 : ℝ)))) *
          (2 * Real.log q)) = 2 * Real.log p := by
        rw [hpP, Finset.sum_singleton, Finset.erase_singleton]
        simp
      have hpmem : p ∈ n.primeFactors := by
        rw [← hP, hpP]
        exact Finset.mem_singleton_self p
      have hmin : n.minFac = p := by
        have hm : n.minFac ∈ n.primeFactors := by
          rw [Nat.mem_primeFactors]
          exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩
        rw [← hP, hpP] at hm
        exact Finset.mem_singleton.mp hm
      have hpp : IsPrimePow n :=
        (isPrimePow_iff_card_primeFactors_eq_one).mpr (by rw [← hP, h1])
      have hLam : Λ n = Real.log p := by
        rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp, hmin]
      convert hmul using 2
      simp [hprod0, hD, hLam]
    · have hD : (∑ q ∈ P, (∏ j ∈ P.erase q, (1 - (j : ℝ) ^ (-2 * (0 : ℝ)))) *
          (2 * Real.log q)) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        have hne : (P.erase q).Nonempty := by
          have hcarde : 1 ≤ (P.erase q).card := by
            rw [Finset.card_erase_of_mem hq]
            omega
          exact Finset.card_pos.mp hcarde
        obtain ⟨r, hr⟩ := hne
        rw [Finset.prod_eq_zero hr (hf0 r)]
        norm_num
      have hnpp : ¬IsPrimePow n := by
        intro h
        rw [isPrimePow_iff_card_primeFactors_eq_one, ← hP] at h
        omega
      have hLam : Λ n = 0 := by
        by_contra h
        exact hnpp ((ArithmeticFunction.vonMangoldt_ne_zero_iff).mp h)
      convert hmul using 2
      simp [hprod0, hD, hLam]

/-- The summatory derivative: `∂_ω A_ω(X)|₀ = 2 ∑_{n ≤ X} Λ(n)`. -/
theorem hasDerivAt_suzukiShiftedSummatory (X : ℕ) :
    HasDerivAt (fun ω => suzukiShiftedSummatory ω X)
      (2 * ∑ n ∈ Finset.Icc 1 X, Λ n) 0 := by
  rw [suzukiShiftedSummatory, Finset.mul_sum]
  exact HasDerivAt.sum fun n hn =>
    hasDerivAt_suzukiShiftedCoefficient (Finset.mem_Icc.mp hn).1

/-- The finite von Mangoldt sum is the Chebyshev `ψ` function at integer points. -/
theorem sum_Icc_vonMangoldt_eq_psi (X : ℕ) :
    ∑ n ∈ Finset.Icc 1 X, Λ n = ψ (X : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  · intro n _
    rfl

/-- **Residue transport.**  The real scalar form of the zeta residue at `s = 1` along the
real ray `1 + 2ω`. -/
theorem tendsto_omega_mul_riemannZeta_re_one_add_two_mul :
    Tendsto (fun ω : ℝ => ω * (riemannZeta (((1 + 2 * ω : ℝ) : ℂ))).re)
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h1 : Tendsto (fun ω : ℝ => (((1 + 2 * ω : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have hcont : Tendsto (fun ω : ℝ => (1 : ℝ) + 2 * ω) (𝓝 0) (𝓝 1) := by
        have := (tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_id (x := (0 : ℝ))).const_mul (2 : ℝ))
        simpa using this
      have hcomp := (Complex.continuous_ofReal.tendsto 1).comp hcont
      exact hcomp.mono_left nhdsWithin_le_nhds
    · exact eventually_of_mem self_mem_nhdsWithin fun ω hω => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.ofReal_re, Complex.one_re] at hre
        linarith [hω]
  have h2 := riemannZeta_residue_one.comp h1
  have h3 : Tendsto (fun ω : ℝ => (((2 * ω : ℝ)) : ℂ) *
      riemannZeta (((1 + 2 * ω : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 1) := by
    refine h2.congr' (eventually_of_mem self_mem_nhdsWithin fun ω hω => ?_)
    congr 1
    push_cast
    ring
  have h4 := (Complex.continuous_re.tendsto 1).comp h3
  have h5 : Tendsto (fun ω : ℝ => 2 * (ω * (riemannZeta (((1 + 2 * ω : ℝ) : ℂ))).re))
      (𝓝[>] 0) (𝓝 1) := by
    refine h4.congr' (eventually_of_forall fun ω => ?_)
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h6 := h5.const_mul (1 / 2 : ℝ)
  refine h6.congr' (eventually_of_forall fun ω => ?_)
  ring

/-- The normalized main term has the exact critical slope: `M_ω(X) / ω → 2X`. -/
theorem suzukiMainTerm_tendsto_ratio (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun ω => suzukiMainTerm ω X / ω) (𝓝[>] 0) (𝓝 (2 * X)) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hzeta := tendsto_omega_mul_riemannZeta_re_one_add_two_mul
  have hpow : Tendsto (fun ω : ℝ => (X : ℝ) ^ (1 + ω)) (𝓝[>] 0) (𝓝 X) := by
    have h1 : Tendsto (fun ω : ℝ => Real.log X * (1 + ω)) (𝓝 0) (𝓝 (Real.log X)) := by
      have hmul := (tendsto_const_nhds (x := Real.log X)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_id (x := (0 : ℝ))))
      simpa using hmul
    have h2 := h1.exp
    rw [Real.exp_log hX0] at h2
    refine (h2.mono_left nhdsWithin_le_nhds).congr'
      (eventually_of_forall fun ω => ?_)
    rw [Real.rpow_def_of_pos hX0]
    ring_nf
  have hone : Tendsto (fun ω : ℝ => (1 : ℝ) + ω) (𝓝[>] 0) (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add (tendsto_id (x := (0 : ℝ)))
    simpa using h.mono_left nhdsWithin_le_nhds
  have hmain := (hpow.div hone one_ne_zero).div hzeta (by norm_num)
  have hval : (X : ℝ) / 1 / (1 / 2) = 2 * X := by ring
  rw [hval] at hmain
  refine hmain.congr' (eventually_of_mem self_mem_nhdsWithin fun ω hω => ?_)
  have hω0 : ω ≠ 0 := ne_of_gt hω
  simp only [suzukiMainTerm]
  field_simp
  ring

/-- The base value `A_0(X) = 1`: at `ω = 0` every shifted coefficient vanishes except `c_0(1)`. -/
theorem suzukiShiftedSummatory_zero (X : ℕ) (hX : 1 ≤ X) :
    suzukiShiftedSummatory 0 X = 1 := by
  rw [suzukiShiftedSummatory]
  rw [Finset.sum_eq_single 1]
  · simp [suzukiShiftedCoefficient]
  · intro n hn hn1
    have hn2 : 2 ≤ n := by omega
    have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hn2
    obtain ⟨p, hp⟩ := hne
    rw [suzukiShiftedCoefficient]
    rw [Finset.prod_eq_zero hp (by simp : (1 : ℝ) - (p : ℝ) ^ (-2 * (0 : ℝ)) = 0)]
    simp
  · intro h
    exact h (Finset.mem_Icc.mpr ⟨le_refl 1, hX⟩)

/-- **Critical derivative law for the Suzuki coupled error.**  Measured from its critical base
value `A_0(X)` (the all-prime main term `M_ω(X)` vanishes at the critical exponent, since
`ζ(1+2ω)` has its pole there), the right derivative of the coupled summatory error
`E_ω(X) = A_ω(X) - M_ω(X)` at `ω = 0` is exactly `2 (ψ(X) - X)`: the infinitesimal Euler
leakage is the Chebyshev error. -/
theorem suzukiCoupledError_critical_derivative (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun ω => (suzukiCoupledError ω X - suzukiShiftedSummatory 0 X) / ω)
      (𝓝[>] 0) (𝓝 (2 * ψ (X : ℝ) - 2 * X)) := by
  have hA := hasDerivAt_suzukiShiftedSummatory X
  have hslope : Tendsto
      (fun ω => (suzukiShiftedSummatory ω X - suzukiShiftedSummatory 0 X) / ω)
      (𝓝[>] 0) (𝓝 (2 * ∑ n ∈ Finset.Icc 1 X, Λ n)) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hA
    have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 :=
      nhdsWithin_mono_right fun ω hω => ne_of_gt hω
    refine (h.mono_left hmono).congr' (eventually_of_forall fun ω => ?_)
    simp [sub_zero, div_eq_mul_inv, smul_eq_mul, mul_comm]
  have hM := suzukiMainTerm_tendsto_ratio X hX
  have hsub := hslope.sub hM
  have hcongr : (fun ω => ((suzukiShiftedSummatory ω X - suzukiShiftedSummatory 0 X) / ω -
      suzukiMainTerm ω X / ω)) =ᶠ[𝓝[>] 0]
      (fun ω => (suzukiCoupledError ω X - suzukiShiftedSummatory 0 X) / ω) := by
    apply eventuallyEq_of_mem self_mem_nhdsWithin
    intro ω hω
    have hω0 : ω ≠ 0 := ne_of_gt hω
    simp only [suzukiCoupledError]
    field_simp
    ring
  have h := Tendsto.congr' hcongr hsub
  rw [sum_Icc_vonMangoldt_eq_psi X] at h
  exact h

/-- The derivative law at the explicit base value `A_0(X) = 1`. -/
theorem suzukiCoupledError_critical_derivative_base_one (X : ℕ) (hX : 1 ≤ X) :
    Tendsto (fun ω => (suzukiCoupledError ω X - 1) / ω)
      (𝓝[>] 0) (𝓝 (2 * ψ (X : ℝ) - 2 * X)) := by
  rw [← suzukiShiftedSummatory_zero X hX]
  exact suzukiCoupledError_critical_derivative X hX

end
