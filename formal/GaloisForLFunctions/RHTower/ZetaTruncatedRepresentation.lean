import GaloisForLFunctions.RHTower.ZetaUnitIntervalIntegrals

/-!
# The truncated representation of ζ on `Re s > 1`

`ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - s·∫_N^∞ {u}·u^{-s-1} du`.

The floor-weighted tail integral telescopes over unit intervals into
`(N^{1-s} + Σ_{n>N} n^{-s})/s`, the fractional part splits it against
the exact power integral, and the Dirichlet series recombines.  This is
the identity whose analytic continuation to `Re s > 0` carries the
vertical growth bounds `|ζ(σ+it)| = O(log t)` behind the de la Vallée
Poussin zero-free region.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter

section

variable {s : ℂ} {N : ℕ}

/-- Integrability of the floor-weighted tail integrand. -/
theorem integrableOn_Ici_natFloor_cpow (hs : 1 < s.re) (hN : 1 ≤ N) :
    IntegrableOn (fun u : ℝ => ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (Set.Ici (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hg : IntegrableOn (fun u : ℝ => u ^ (-s.re)) (Set.Ici (N : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hN0
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (volume.restrict (Set.Ici (N : ℝ))) := by
    apply AEStronglyMeasurable.mul
    · exact (Complex.measurable_ofReal.comp
        (measurable_from_top.comp Nat.measurable_floor)).aestronglyMeasurable
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ici
      intro u hu
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hN0 hu
      have h2 : Continuous fun v : ℝ => (v, (-s - 1 : ℂ)) := by fun_prop
      exact ((Complex.continuousAt_ofReal_cpow u (-s - 1)
        (Or.inr (ne_of_gt hu0))).comp
          (f := fun v : ℝ => (v, (-s - 1 : ℂ)))
          h2.continuousAt).continuousWithinAt
  apply Integrable.mono hg hmeas
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards with u hu
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le hN0 hu
  have h1 : ‖((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)‖
      = (⌊u⌋₊ : ℝ) * u ^ ((-s - 1).re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu0,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (⌊u⌋₊ : ℝ))]
  rw [h1, show (-s - 1).re = -s.re - 1 by
      simp [Complex.sub_re, Complex.neg_re]]
  have h3 : ‖u ^ (-s.re)‖ = u ^ (-s.re) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hu0.le _)]
  rw [h3]
  have h4 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0.le
  have h5 : u * u ^ (-s.re - 1) = u ^ (-s.re) := by
    rw [show u * u ^ (-s.re - 1) = u ^ (1 : ℝ) * u ^ (-s.re - 1) by
        rw [Real.rpow_one],
      ← Real.rpow_add hu0]
    norm_num
  rw [← h5]
  have h6 : (0 : ℝ) ≤ u ^ (-s.re - 1) := Real.rpow_nonneg hu0.le _
  nlinarith

set_option maxHeartbeats 3200000 in
/-- **Truncated representation of ζ** on `Re s > 1`. -/
theorem zeta_eq_truncated (hs : 1 < s.re) (hN : 1 ≤ N) :
    riemannZeta s = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
      + (N : ℂ) ^ (1 - s) / (s - 1) - s * zetaSawtoothTail N s := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hs0 : (0 : ℝ) < s.re := by linarith
  have hsne0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
  have hsne1 : s - 1 ≠ 0 := fun h => by
    have : s = 1 := by linear_combination h
    rw [this] at hs
    simp at hs
  have hNC0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : N ≠ 0)
  -- PART 1: the floor telescope `s·T = N^{1-s} + Tζ`
  have hsumT := hasSum_integral_Ico_unit (c := (N : ℝ))
    (integrableOn_Ici_natFloor_cpow hs hN)
  have hpieceEq : (fun k : ℕ => ∫ u in
      Set.Ico ((N : ℝ) + k) ((N : ℝ) + k + 1),
        ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      = fun k : ℕ => (((N : ℝ) + k : ℝ) : ℂ)
          * ((((N : ℝ) + k : ℝ) : ℂ) ^ (-s)
            - (((N : ℝ) + k + 1 : ℝ) : ℂ) ^ (-s)) / s := by
    funext k
    have hck : (0 : ℝ) < (N : ℝ) + k := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hfloor : ∀ u ∈ Set.Ico ((N : ℝ) + k) ((N : ℝ) + k + 1),
        ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
          = (((N : ℝ) + k : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
      intro u hu
      rw [Set.mem_Ico] at hu
      have hfl : ⌊u⌋₊ = N + k := by
        rw [Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ u)]
        constructor
        · push_cast
          linarith
        · push_cast
          linarith
      rw [hfl]
      congr 1
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ico hfloor,
      integral_const_mul, integral_Ico_eq_integral_Ioc,
      integral_Ioc_ofReal_cpow hck (by linarith)
        (fun h => hsne0 (by linear_combination -h)),
      show (-s - 1 + 1 : ℂ) = -s by ring]
    field_simp
    ring
  rw [hpieceEq] at hsumT
  have hsumT2 := hsumT.mul_left s
  have hsimp : (fun k : ℕ => s * ((((N : ℝ) + k : ℝ) : ℂ)
      * ((((N : ℝ) + k : ℝ) : ℂ) ^ (-s)
        - (((N : ℝ) + k + 1 : ℝ) : ℂ) ^ (-s)) / s))
      = fun k : ℕ => ((((N : ℝ) + k : ℝ) : ℂ)
          * ((((N : ℝ) + k : ℝ) : ℂ) ^ (-s)
            - (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s))) := by
    funext k
    rw [show (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ)
        = (((N : ℝ) + k + 1 : ℝ) : ℂ) by push_cast; ring]
    field_simp
  rw [hsimp] at hsumT2
  -- the split into telescope + shifted ζ-tail
  have hstep : (fun k : ℕ => ((((N : ℝ) + k : ℝ) : ℂ)
      * ((((N : ℝ) + k : ℝ) : ℂ) ^ (-s)
        - (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s))))
      = fun k : ℕ => (((((N : ℝ) + k : ℝ) : ℂ)
            * (((N : ℝ) + k : ℝ) : ℂ) ^ (-s)
          - ((((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ)
            * (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)))
        + (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)) := by
    funext k
    have hA : (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ)
        = (((N : ℝ) + k : ℝ) : ℂ) + 1 := by
      push_cast
      ring
    rw [hA]
    ring
  rw [hstep] at hsumT2
  -- the shifted ζ-tail sums
  have hsummable : Summable fun n : ℕ => 1 / (n : ℂ) ^ s :=
    Complex.summable_one_div_nat_cpow.2 hs
  have htermEq : (fun k : ℕ => 1 / ((k + (N + 1) : ℕ) : ℂ) ^ s)
      = fun k : ℕ => (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s) := by
    funext k
    rw [Complex.cpow_neg, inv_eq_one_div]
    congr 2
    push_cast
    ring
  have hsummable2 : Summable
      (fun k : ℕ => (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)) := by
    rw [← htermEq]
    exact ((summable_nat_add_iff (N + 1)).2 hsummable)
  have hsumTail := hsummable2.hasSum
  have hsub := hsumT2.sub hsumTail
  have hsimp2 : (fun k : ℕ => ((((((N : ℝ) + k : ℝ) : ℂ)
        * (((N : ℝ) + k : ℝ) : ℂ) ^ (-s)
      - ((((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ)
        * (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)))
      + (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s))
      - (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s)))
      = fun k : ℕ => ((((N : ℝ) + k : ℝ) : ℂ)
          * (((N : ℝ) + k : ℝ) : ℂ) ^ (-s)
        - ((((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ)
          * (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s))) := by
    funext k
    ring
  rw [hsimp2] at hsub
  -- the telescope head
  have hf0 : Tendsto (fun k : ℕ => (((N : ℝ) + k : ℝ) : ℂ)
      * (((N : ℝ) + k : ℝ) : ℂ) ^ (-s)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hnorm : ∀ k : ℕ, ‖(((N : ℝ) + k : ℝ) : ℂ)
        * (((N : ℝ) + k : ℝ) : ℂ) ^ (-s)‖
        = ((N : ℝ) + k) ^ (1 - s.re) := by
      intro k
      have hck : (0 : ℝ) < (N : ℝ) + k := by
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hck,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hck,
        show (-s).re = -s.re by simp,
        show (1 : ℝ) - s.re = 1 + -s.re by ring,
        Real.rpow_add hck, Real.rpow_one]
    simp only [hnorm]
    have h1 : Tendsto (fun k : ℕ => ((N : ℝ) + k)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun x : ℝ => x ^ (1 - s.re)) atTop (nhds 0) := by
      have h3 := tendsto_rpow_neg_atTop
        (show (0 : ℝ) < -(1 - s.re) by linarith)
      simpa using h3
    exact h2.comp h1
  have hkey := eq_head_of_hasSum_telescope hsub hf0
  rw [show (((N : ℝ) + ((0 : ℕ) : ℝ) : ℝ) : ℂ) = (N : ℂ) by
    push_cast; ring] at hkey
  have hhead : (N : ℂ) * (N : ℂ) ^ (-s) = (N : ℂ) ^ (1 - s) := by
    rw [show (1 - s : ℂ) = 1 + -s by ring,
      Complex.cpow_add _ _ hNC0, Complex.cpow_one]
  rw [hhead] at hkey
  -- PART 2: the fract split of the sawtooth tail
  have hint_pow : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (-s))
      (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ici_ofReal_cpow hN0
      (by simp only [Complex.neg_re]; linarith)).mono_set
      Set.Ioi_subset_Ici_self
  have hint_floor : IntegrableOn
      (fun u : ℝ => ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1))
      (Set.Ioi (N : ℝ)) :=
    (integrableOn_Ici_natFloor_cpow hs hN).mono_set Set.Ioi_subset_Ici_self
  have hfractEq : ∀ u ∈ Set.Ioi (N : ℝ),
      ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
        = (u : ℂ) ^ (-s)
          - ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    intro u hu
    rw [Set.mem_Ioi] at hu
    have hu0 : (0 : ℝ) < u := lt_trans hN0 hu
    have hfr : Int.fract u = u - (⌊u⌋₊ : ℝ) := by
      rw [← Int.self_sub_floor]
      congr 1
      exact_mod_cast (Int.natCast_floor_eq_floor hu0.le).symm
    have hpow : (u : ℂ) * (u : ℂ) ^ (-s - 1) = (u : ℂ) ^ (-s) := by
      rw [show (u : ℂ) * (u : ℂ) ^ (-s - 1)
          = (u : ℂ) ^ (1 : ℂ) * (u : ℂ) ^ (-s - 1) by rw [Complex.cpow_one],
        ← Complex.cpow_add _ _ (by exact_mod_cast ne_of_gt hu0)]
      norm_num
    rw [hfr, ← hpow]
    push_cast
    ring
  have hsplit : zetaSawtoothTail N s
      = (∫ u in Set.Ioi (N : ℝ), (u : ℂ) ^ (-s))
        - ∫ u in Set.Ioi (N : ℝ),
            ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1) := by
    rw [zetaSawtoothTail,
      setIntegral_congr_fun measurableSet_Ioi hfractEq,
      integral_sub hint_pow hint_floor]
  have hpowval : ∫ u in Set.Ioi (N : ℝ), (u : ℂ) ^ (-s)
      = (N : ℂ) ^ (1 - s) / (s - 1) := by
    rw [← integral_Ici_eq_integral_Ioi,
      integral_Ici_ofReal_cpow hN0
        (by simp only [Complex.neg_re]; linarith),
      show (-s + 1 : ℂ) = 1 - s by ring]
    have h1s : (1 : ℂ) - s ≠ 0 := fun h => hsne1 (by linear_combination -h)
    rw [div_eq_div_iff h1s hsne1]
    push_cast
    ring
  -- PART 3: the ζ side
  have hzeta : riemannZeta s
      = (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
        + ∑' k : ℕ, (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s) := by
    rw [zeta_eq_tsum_one_div_nat_cpow hs,
      ← hsummable.sum_add_tsum_nat_add (N + 1)]
    congr 1
    · rw [Finset.sum_range_succ']
      have h0 : 1 / ((0 : ℕ) : ℂ) ^ s = 0 := by
        rw [Nat.cast_zero, Complex.zero_cpow hsne0]
        simp
      rw [h0, add_zero]
      apply Finset.sum_nbij' (i := fun i => i + 1) (j := fun n => n - 1)
      · intro i hi
        rw [Finset.mem_range] at hi
        rw [Finset.mem_Icc]
        omega
      · intro n hn
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_range]
        omega
      · intro i _
        omega
      · intro n hn
        rw [Finset.mem_Icc] at hn
        omega
      · intro i _
        rw [Complex.cpow_neg, inv_eq_one_div]
    · exact tsum_congr fun k => by
        rw [Complex.cpow_neg, inv_eq_one_div]
        congr 2
        push_cast
        ring
  -- FINAL assembly
  have hT : s * ∫ u in Set.Ioi (N : ℝ),
      ((⌊u⌋₊ : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
      = (N : ℂ) ^ (1 - s)
        + ∑' k : ℕ, (((N : ℝ) + (k + 1 : ℕ) : ℝ) : ℂ) ^ (-s) := by
    rw [← integral_Ici_eq_integral_Ioi]
    linear_combination hkey
  rw [hzeta, hsplit]
  have hTζ := hT
  -- solve linearly: tail = pow/(s-1) − T and sT = N^{1-s} + Tζ
  rw [hpowval]
  have hinv : (s - 1) * (s - 1)⁻¹ = 1 := mul_inv_cancel₀ hsne1
  linear_combination -hTζ + (N : ℂ) ^ (1 - s) * hinv

end

end RHTower
