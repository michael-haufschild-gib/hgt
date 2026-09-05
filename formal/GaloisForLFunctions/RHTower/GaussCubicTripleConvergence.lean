import GaloisForLFunctions.RHTower.GaussFarBandMarginal

/-!
# Vanishing of the literal cubic triple-defect contribution

The three-component Gauss conservation law caps the product of the three squared ratio defects.
The coordinate marginals of the true convolution kernel make each resulting far band summable.
-/

namespace RHTower

open Filter Topology GaloisForLFunctions
open scoped ENNReal

noncomputable section

def gaussCubicTripleDominatingBound (k : Fin 3) (p : Nat.Primes) (i : ℤ) : ℝ≥0∞ :=
  ∑' jlr : ℤ × (ℤ × ℤ), ENNReal.ofReal
    (gaussCubicTripleDominatingKernel p jlr.1 jlr.2.1 jlr.2.2 *
      ‖gaussSampleRatioDefect k p jlr.1 i‖ ^ 2 *
        ‖gaussSampleRatioDefect k p jlr.2.1 i‖ ^ 2 *
          ‖gaussSampleRatioDefect k p jlr.2.2 i‖ ^ 2)

def gaussCubicTripleSwapJL : ℤ × (ℤ × ℤ) ≃ ℤ × (ℤ × ℤ) where
  toFun a := (a.2.1, (a.1, a.2.2))
  invFun a := (a.2.1, (a.1, a.2.2))
  left_inv a := by rcases a with ⟨j, l, r⟩; rfl
  right_inv a := by rcases a with ⟨l, j, r⟩; rfl

def gaussCubicTripleSwapJR : ℤ × (ℤ × ℤ) ≃ ℤ × (ℤ × ℤ) where
  toFun a := (a.2.2, (a.2.1, a.1))
  invFun a := (a.2.2, (a.2.1, a.1))
  left_inv a := by rcases a with ⟨j, l, r⟩; rfl
  right_inv a := by rcases a with ⟨r, l, j⟩; rfl

theorem gaussCubicTripleDefectBound_le_dominating
    (k : Fin 3) (p : Nat.Primes) (i : ℤ) :
    gaussCubicTripleDefectBound k p i ≤ gaussCubicTripleDominatingBound k p i := by
  rw [gaussCubicTripleDefectBound, gaussCubicTripleDominatingBound,
    ENNReal.tsum_prod']
  refine ENNReal.tsum_le_tsum fun j => ?_
  set ρj : ℝ := ‖gaussSampleRatioDefect k p j i‖ with hρj
  set q : ℝ := gaussCubicTripleKernelMassConstant p /
    (1 + (j.natAbs : ℝ)) ^ ((2 : ℝ) / 3) with hq
  have hρjnn : 0 ≤ ρj := by rw [hρj]; exact norm_nonneg _
  have hqnn : 0 ≤ q := by
    rw [hq]
    exact div_nonneg (gaussCubicTripleKernelMassConstant_nonneg p) (by positivity)
  have hmass := gaussCubicTripleKernelMass_le p j
  rw [← hq] at hmass
  set B : ℝ≥0∞ := ∑' lr : ℤ × ℤ, ENNReal.ofReal
    (gaussCubicTripleCoeffKernel p j lr.1 lr.2 *
      ‖gaussSampleRatioDefect k p lr.1 i‖ ^ 2 *
        ‖gaussSampleRatioDefect k p lr.2 i‖ ^ 2) with hB
  calc
    ENNReal.ofReal (ρj ^ 2) * gaussCubicTripleKernelMass p j * B
        ≤ ENNReal.ofReal (ρj ^ 2) * ENNReal.ofReal q * B := by
          exact mul_le_mul' (mul_le_mul' le_rfl hmass) le_rfl
    _ = ∑' lr : ℤ × ℤ, ENNReal.ofReal
        (gaussCubicTripleDominatingKernel p j lr.1 lr.2 * ρj ^ 2 *
          ‖gaussSampleRatioDefect k p lr.1 i‖ ^ 2 *
            ‖gaussSampleRatioDefect k p lr.2 i‖ ^ 2) := by
      rw [hB, ← ENNReal.tsum_mul_left]
      exact tsum_congr fun lr => by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [gaussCubicTripleDominatingKernel, ← hq]
        ring

theorem tsum_ofReal_gaussCubicTripleDominatingKernel_ne_top (p : Nat.Primes) :
    (∑' jlr : ℤ × (ℤ × ℤ), ENNReal.ofReal
      (gaussCubicTripleDominatingKernel p jlr.1 jlr.2.1 jlr.2.2)) ≠ ⊤ := by
  have hstep : ∀ j : ℤ,
      (∑' lr : ℤ × ℤ, ENNReal.ofReal
        (gaussCubicTripleDominatingKernel p j lr.1 lr.2)) ≤
        ENNReal.ofReal (gaussCubicTripleKernelMassConstant p ^ 2) *
          intPowWeight ((4 : ℝ) / 3) j := by
    intro j
    refine (tsum_gaussCubicTripleDominatingKernel_jMarginal_le p j).trans_eq ?_
    rw [intPowWeight, ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [natAbs_cast_eq_abs]
    ring
  have htotal : (∑' jlr : ℤ × (ℤ × ℤ), ENNReal.ofReal
      (gaussCubicTripleDominatingKernel p jlr.1 jlr.2.1 jlr.2.2)) ≤
      ENNReal.ofReal (gaussCubicTripleKernelMassConstant p ^ 2) *
        ∑' j : ℤ, intPowWeight ((4 : ℝ) / 3) j := by
    rw [ENNReal.tsum_prod']
    refine (ENNReal.tsum_le_tsum hstep).trans_eq ?_
    rw [ENNReal.tsum_mul_left]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (tsum_intPowWeight_ne_top (by norm_num))) htotal

theorem tendsto_gaussCubicTripleDominatingBound (k : Fin 3) (p : Nat.Primes) :
    Tendsto (fun I : ℕ => gaussCubicTripleDominatingBound k p (I : ℤ))
      atTop (nhds 0) := by
  obtain ⟨K, hK, hcap⟩ := exists_gaussTripleDefectCap k p
  simp only [gaussCubicTripleDominatingBound]
  refine tendsto_tsum_zero_of_dominated
    (F := fun (a : ℤ × (ℤ × ℤ)) (I : ℕ) => ENNReal.ofReal
      (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
        ‖gaussSampleRatioDefect k p a.1 (I : ℤ)‖ ^ 2 *
          ‖gaussSampleRatioDefect k p a.2.1 (I : ℤ)‖ ^ 2 *
            ‖gaussSampleRatioDefect k p a.2.2 (I : ℤ)‖ ^ 2))
    (G := fun (a : ℤ × (ℤ × ℤ)) (_ : ℕ) => ENNReal.ofReal
      (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 * (64 + 72 * K)))
    (H := fun (a : ℤ × (ℤ × ℤ)) (I : ℕ) =>
      (if I < 2 * a.1.natAbs ∧ ((I : ℤ) + a.1).natAbs ≠ 0 then
        ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
          (12 * K * (I : ℝ) / (((I : ℤ) + a.1).natAbs : ℝ))) else 0) +
      ((if I < 2 * a.2.1.natAbs ∧ ((I : ℤ) + a.2.1).natAbs ≠ 0 then
        ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
          (12 * K * (I : ℝ) / (((I : ℤ) + a.2.1).natAbs : ℝ))) else 0) +
      (if I < 2 * a.2.2.natAbs ∧ ((I : ℤ) + a.2.2).natAbs ≠ 0 then
        ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
          (12 * K * (I : ℝ) / (((I : ℤ) + a.2.2).natAbs : ℝ))) else 0)))
    ?_ ?_ ?_ ?_
  · intro a
    have hj := tendsto_gaussSampleRatioDefect_nat (m := 3) (by omega) k p a.1
    have hl := tendsto_gaussSampleRatioDefect_nat (m := 3) (by omega) k p a.2.1
    have hr := tendsto_gaussSampleRatioDefect_nat (m := 3) (by omega) k p a.2.2
    have hjn : Tendsto (fun I : ℕ =>
        ‖gaussSampleRatioDefect k p a.1 (I : ℤ)‖ ^ 2) atTop (nhds 0) := by
      have h := tendsto_zero_iff_norm_tendsto_zero.mp hj
      simpa using h.pow 2
    have hln : Tendsto (fun I : ℕ =>
        ‖gaussSampleRatioDefect k p a.2.1 (I : ℤ)‖ ^ 2) atTop (nhds 0) := by
      have h := tendsto_zero_iff_norm_tendsto_zero.mp hl
      simpa using h.pow 2
    have hrn : Tendsto (fun I : ℕ =>
        ‖gaussSampleRatioDefect k p a.2.2 (I : ℤ)‖ ^ 2) atTop (nhds 0) := by
      have h := tendsto_zero_iff_norm_tendsto_zero.mp hr
      simpa using h.pow 2
    have hprod := (hjn.mul hln).mul hrn
    simp only [mul_zero] at hprod
    have hmul := hprod.const_mul
      (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2)
    rw [mul_zero] at hmul
    have hcont := (ENNReal.continuous_ofReal.tendsto 0).comp hmul
    simpa [Function.comp_def, mul_assoc] using hcont
  · intro a I
    set x : ℝ := gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 with hx
    have hxnn : 0 ≤ x := by
      rw [hx]
      exact gaussCubicTripleDominatingKernel_nonneg p a.1 a.2.1 a.2.2
    have hc := hcap I a.1 a.2.1 a.2.2
    have hnfj := harmonic_factor_near_far (K' := 12 * K) (by positivity) I a.1
    have hnfl := harmonic_factor_near_far (K' := 12 * K) (by positivity) I a.2.1
    have hnfr := harmonic_factor_near_far (K' := 12 * K) (by positivity) I a.2.2
    let J : ℝ := if I < 2 * a.1.natAbs ∧ ((I : ℤ) + a.1).natAbs ≠ 0 then
      x * (12 * K * (I : ℝ) / (((I : ℤ) + a.1).natAbs : ℝ)) else 0
    let L : ℝ := if I < 2 * a.2.1.natAbs ∧ ((I : ℤ) + a.2.1).natAbs ≠ 0 then
      x * (12 * K * (I : ℝ) / (((I : ℤ) + a.2.1).natAbs : ℝ)) else 0
    let R : ℝ := if I < 2 * a.2.2.natAbs ∧ ((I : ℤ) + a.2.2).natAbs ≠ 0 then
      x * (12 * K * (I : ℝ) / (((I : ℤ) + a.2.2).natAbs : ℝ)) else 0
    have hJnn : 0 ≤ J := by simp only [J]; split_ifs <;> positivity
    have hLnn : 0 ≤ L := by simp only [L]; split_ifs <;> positivity
    have hRnn : 0 ≤ R := by simp only [R]; split_ifs <;> positivity
    have hreal : x *
          (‖gaussSampleRatioDefect k p a.1 (I : ℤ)‖ ^ 2 *
            ‖gaussSampleRatioDefect k p a.2.1 (I : ℤ)‖ ^ 2 *
              ‖gaussSampleRatioDefect k p a.2.2 (I : ℤ)‖ ^ 2)
        ≤ x * (64 + 72 * K) + (J + (L + R)) := by
      have h0 := mul_le_mul_of_nonneg_left hc hxnn
      have hj := mul_le_mul_of_nonneg_left hnfj hxnn
      have hl := mul_le_mul_of_nonneg_left hnfl hxnn
      have hr := mul_le_mul_of_nonneg_left hnfr hxnn
      simp only [mul_add, mul_ite, mul_zero] at hj hl hr
      change x * (12 * K * (I : ℝ) / (((I : ℤ) + a.1).natAbs : ℝ)) ≤
        x * (2 * (12 * K)) + J at hj
      change x * (12 * K * (I : ℝ) / (((I : ℤ) + a.2.1).natAbs : ℝ)) ≤
        x * (2 * (12 * K)) + L at hl
      change x * (12 * K * (I : ℝ) / (((I : ℤ) + a.2.2).natAbs : ℝ)) ≤
        x * (2 * (12 * K)) + R at hr
      nlinarith
    have hconvJ : ENNReal.ofReal J =
        (if I < 2 * a.1.natAbs ∧ ((I : ℤ) + a.1).natAbs ≠ 0 then
          ENNReal.ofReal (x *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.1).natAbs : ℝ))) else 0) := by
      simp only [J]
      split_ifs <;> simp
    have hconvL : ENNReal.ofReal L =
        (if I < 2 * a.2.1.natAbs ∧ ((I : ℤ) + a.2.1).natAbs ≠ 0 then
          ENNReal.ofReal (x *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.2.1).natAbs : ℝ))) else 0) := by
      simp only [L]
      split_ifs <;> simp
    have hconvR : ENNReal.ofReal R =
        (if I < 2 * a.2.2.natAbs ∧ ((I : ℤ) + a.2.2).natAbs ≠ 0 then
          ENNReal.ofReal (x *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.2.2).natAbs : ℝ))) else 0) := by
      simp only [R]
      split_ifs <;> simp
    refine (ENNReal.ofReal_le_ofReal (by simpa only [mul_assoc] using hreal)).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg hxnn (by positivity))
      (add_nonneg hJnn (add_nonneg hLnn hRnn)),
      ENNReal.ofReal_add hJnn (add_nonneg hLnn hRnn),
      ENNReal.ofReal_add hLnn hRnn, hconvJ, hconvL, hconvR, hx]
  · intro ε hε
    have hLnn : 0 ≤ 64 + 72 * K := by positivity
    have htotal : (∑' a : ℤ × (ℤ × ℤ), ENNReal.ofReal
        (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 * (64 + 72 * K))) ≠ ⊤ := by
      have heq : (∑' a : ℤ × (ℤ × ℤ), ENNReal.ofReal
          (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 * (64 + 72 * K))) =
          ENNReal.ofReal (64 + 72 * K) *
            ∑' a : ℤ × (ℤ × ℤ), ENNReal.ofReal
              (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun a => by
          rw [mul_comm, ← ENNReal.ofReal_mul hLnn]
      rw [heq]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (tsum_ofReal_gaussCubicTripleDominatingKernel_ne_top p)
    have htail := ENNReal.tendsto_tsum_compl_atTop_zero htotal
    obtain ⟨S, hS⟩ := (ENNReal.tendsto_nhds_zero.mp htail ε hε).exists
    exact ⟨S, fun _ => hS⟩
  · have hJ : Tendsto (fun I : ℕ => ∑' a : ℤ × (ℤ × ℤ),
        (if I < 2 * a.1.natAbs ∧ ((I : ℤ) + a.1).natAbs ≠ 0 then
          ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.1).natAbs : ℝ))) else 0))
        atTop (nhds 0) := by
      exact tendsto_tsum_prod_farBand_of_marginal
        (W := fun j (lr : ℤ × ℤ) => gaussCubicTripleDominatingKernel p j lr.1 lr.2)
        (C := gaussCubicTripleKernelMassConstant p ^ 2) (D := 12 * K)
        (s := (4 : ℝ) / 3) (sq_nonneg _) (by positivity) (by norm_num)
        (tsum_gaussCubicTripleDominatingKernel_jMarginal_le p)
    have hLbase : Tendsto (fun I : ℕ => ∑' a : ℤ × (ℤ × ℤ),
        (if I < 2 * a.1.natAbs ∧ ((I : ℤ) + a.1).natAbs ≠ 0 then
          ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.2.1 a.1 a.2.2 *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.1).natAbs : ℝ))) else 0))
        atTop (nhds 0) := by
      exact tendsto_tsum_prod_farBand_of_marginal
        (W := fun l (jr : ℤ × ℤ) => gaussCubicTripleDominatingKernel p jr.1 l jr.2)
        (C := gaussCubicTripleLMarginalConstant p) (D := 12 * K)
        (s := (5 : ℝ) / 4) (gaussCubicTripleLMarginalConstant_nonneg p)
        (by positivity) (by norm_num)
        (tsum_gaussCubicTripleDominatingKernel_lMarginal_le p)
    have hL : Tendsto (fun I : ℕ => ∑' a : ℤ × (ℤ × ℤ),
        (if I < 2 * a.2.1.natAbs ∧ ((I : ℤ) + a.2.1).natAbs ≠ 0 then
          ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.2.1).natAbs : ℝ))) else 0))
        atTop (nhds 0) := by
      refine hLbase.congr fun I => ?_
      have hs := Equiv.tsum_eq gaussCubicTripleSwapJL
        (fun a : ℤ × (ℤ × ℤ) =>
          if I < 2 * a.2.1.natAbs ∧ ((I : ℤ) + a.2.1).natAbs ≠ 0 then
            ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
              (12 * K * (I : ℝ) / (((I : ℤ) + a.2.1).natAbs : ℝ))) else 0)
      simpa [gaussCubicTripleSwapJL] using hs
    have hRbase : Tendsto (fun I : ℕ => ∑' a : ℤ × (ℤ × ℤ),
        (if I < 2 * a.1.natAbs ∧ ((I : ℤ) + a.1).natAbs ≠ 0 then
          ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.2.2 a.2.1 a.1 *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.1).natAbs : ℝ))) else 0))
        atTop (nhds 0) := by
      exact tendsto_tsum_prod_farBand_of_marginal
        (W := fun r (lj : ℤ × ℤ) => gaussCubicTripleDominatingKernel p lj.2 lj.1 r)
        (C := gaussCubicTripleRMarginalConstant p) (D := 12 * K)
        (s := (4 : ℝ) / 3) (gaussCubicTripleRMarginalConstant_nonneg p)
        (by positivity) (by norm_num)
        (tsum_gaussCubicTripleDominatingKernel_rMarginal_le p)
    have hR : Tendsto (fun I : ℕ => ∑' a : ℤ × (ℤ × ℤ),
        (if I < 2 * a.2.2.natAbs ∧ ((I : ℤ) + a.2.2).natAbs ≠ 0 then
          ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
            (12 * K * (I : ℝ) / (((I : ℤ) + a.2.2).natAbs : ℝ))) else 0))
        atTop (nhds 0) := by
      refine hRbase.congr fun I => ?_
      have hs := Equiv.tsum_eq gaussCubicTripleSwapJR
        (fun a : ℤ × (ℤ × ℤ) =>
          if I < 2 * a.2.2.natAbs ∧ ((I : ℤ) + a.2.2).natAbs ≠ 0 then
            ENNReal.ofReal (gaussCubicTripleDominatingKernel p a.1 a.2.1 a.2.2 *
              (12 * K * (I : ℝ) / (((I : ℤ) + a.2.2).natAbs : ℝ))) else 0)
      simpa [gaussCubicTripleSwapJR] using hs
    have hsum := hJ.add (hL.add hR)
    simp only [add_zero] at hsum
    refine hsum.congr fun I => ?_
    rw [ENNReal.tsum_add, ENNReal.tsum_add]

theorem tendsto_gaussCubicTripleDefectBound (k : Fin 3) (p : Nat.Primes) :
    Tendsto (fun I : ℕ => gaussCubicTripleDefectBound k p (I : ℤ))
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_gaussCubicTripleDominatingBound k p) (fun _ => bot_le)
    (fun I => gaussCubicTripleDefectBound_le_dominating k p (I : ℤ))

theorem gaussCubicTripleDominatingKernel_neg
    (p : Nat.Primes) (j l r : ℤ) :
    gaussCubicTripleDominatingKernel p (-j) (-l) (-r) =
      gaussCubicTripleDominatingKernel p j l r := by
  have hjl : ((-l : ℤ) - (-j)).natAbs = (l - j).natAbs := by omega
  have hlr : ((-r : ℤ) - (-l)).natAbs = (r - l).natAbs := by omega
  rw [gaussCubicTripleDominatingKernel, gaussCubicTripleDominatingKernel,
    gaussCubicTripleCoeffKernel, gaussCubicTripleCoeffKernel,
    gaussPrimeScaleSqCoeffKernel, gaussPrimeScaleSqCoeffKernel,
    gaussDoubleDefectCoeffKernel, gaussDoubleDefectCoeffKernel,
    Int.natAbs_neg, Int.natAbs_neg, hjl, hlr]

theorem gaussCubicTripleDominatingBound_neg
    (k : Fin 3) (p : Nat.Primes) (i : ℤ) :
    gaussCubicTripleDominatingBound k p (-i) =
      gaussCubicTripleDominatingBound k p i := by
  let e : ℤ × (ℤ × ℤ) ≃ ℤ × (ℤ × ℤ) :=
    (Equiv.neg ℤ).prodCongr ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ))
  rw [gaussCubicTripleDominatingBound, gaussCubicTripleDominatingBound,
    ← e.tsum_eq]
  refine tsum_congr fun a => ?_
  rcases a with ⟨j, l, r⟩
  have happly : e (j, (l, r)) = (-j, (-l, -r)) := by
    simp [e, Equiv.prodCongr_apply, Equiv.neg_apply]
  rw [happly, gaussCubicTripleDominatingKernel_neg]
  have hρ : ∀ x : ℤ, ‖gaussSampleRatioDefect k p (-x) (-i)‖ =
      ‖gaussSampleRatioDefect k p x i‖ := by
    intro x
    rw [gaussSampleRatioDefect_neg, RCLike.norm_conj]
  rw [hρ j, hρ l, hρ r]

theorem gaussCubicTripleDominatingBound_natAbs
    (k : Fin 3) (p : Nat.Primes) (i : ℤ) :
    gaussCubicTripleDominatingBound k p ((i.natAbs : ℤ)) =
      gaussCubicTripleDominatingBound k p i := by
  rcases Int.natAbs_eq i with h | h
  · rw [← h]
  · have hb := gaussCubicTripleDominatingBound_neg k p ((i.natAbs : ℤ))
    rw [← h] at hb
    exact hb.symm

theorem tendsto_gaussCubicTripleDominatingBound_comp
    (k : Fin 3) (p : Nat.Primes) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ => gaussCubicTripleDominatingBound k p (ι n))
      atTop (nhds 0) := by
  have hcomp := (tendsto_gaussCubicTripleDominatingBound k p).comp hι
  refine hcomp.congr fun n => ?_
  simp only [Function.comp_apply]
  exact gaussCubicTripleDominatingBound_natAbs k p (ι n)

theorem tendsto_gaussCubicTripleDefectBound_comp
    (k : Fin 3) (p : Nat.Primes) {ι : ℕ → ℤ}
    (hι : Tendsto (fun n : ℕ => (ι n).natAbs) atTop atTop) :
    Tendsto (fun n : ℕ => gaussCubicTripleDefectBound k p (ι n))
      atTop (nhds 0) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_gaussCubicTripleDominatingBound_comp k p hι) (fun _ => bot_le)
    (fun n => gaussCubicTripleDefectBound_le_dominating k p (ι n))

end

end RHTower
