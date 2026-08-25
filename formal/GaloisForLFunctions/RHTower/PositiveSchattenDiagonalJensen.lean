import GaloisForLFunctions.RHTower.PositiveOperatorTraceComparison

/-!
# Jensen control of positive Schatten diagonals

For `q ≥ 1`, convexity of `x ↦ x ^ q` turns the singular-vector expansion of a
positive compact operator into the sharp diagonal estimate

`∑ᵢ ⟨gᵢ, T gᵢ⟩ ^ q ≤ ∑ₙ sₙ(T) ^ q`

for every orthonormal-with-zeros family.  This is the operator-theoretic converse engine in the
doubling-Fock Toeplitz criterion: lower bounds for localized diagonal tests force the corresponding
cell averages to be `q`-summable.
-/

namespace RHTower

noncomputable section

open Finset

/-- Jensen's inequality for a finite nonnegative weighted sum of total weight at most one. -/
theorem finset_weighted_sum_rpow_le_sum_weighted_rpow
    {ι : Type*} (s : Finset ι) (w a : ι → ℝ) {q : ℝ}
    (hq : 1 ≤ q) (hw0 : ∀ i ∈ s, 0 ≤ w i)
    (ha0 : ∀ i ∈ s, 0 ≤ a i) (hw1 : ∑ i ∈ s, w i ≤ 1) :
    (∑ i ∈ s, w i * a i) ^ q ≤ ∑ i ∈ s, w i * a i ^ q := by
  let W : ℝ := ∑ i ∈ s, w i
  let A : ℝ := ∑ i ∈ s, w i * a i
  let B : ℝ := ∑ i ∈ s, w i * a i ^ q
  change A ^ q ≤ B
  have hW0 : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i hi => hw0 i hi
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw0 i hi) (ha0 i hi)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw0 i hi) (Real.rpow_nonneg (ha0 i hi) q)
  by_cases hW : W = 0
  · have hwzero : ∀ i ∈ s, w i = 0 := by
      intro i hi
      have hle : w i ≤ W := by
        dsimp [W]
        exact Finset.single_le_sum (fun j hj => hw0 j hj) hi
      exact le_antisymm (by simpa [hW] using hle) (hw0 i hi)
    have hAz : A = 0 := by
      dsimp [A]
      exact Finset.sum_eq_zero fun i hi => by rw [hwzero i hi, zero_mul]
    have hBz : B = 0 := by
      dsimp [B]
      exact Finset.sum_eq_zero fun i hi => by rw [hwzero i hi, zero_mul]
    rw [hAz, hBz, Real.zero_rpow (by linarith : q ≠ 0)]
  · have hWpos : 0 < W := lt_of_le_of_ne hW0 (Ne.symm hW)
    have hj := (convexOn_rpow hq).map_centerMass_le
      (t := s) (w := w) (p := a) hw0 (by simpa [W] using hWpos)
      (fun i hi => Set.mem_Ici.mpr (ha0 i hi))
    have hj' : (W⁻¹ * A) ^ q ≤ W⁻¹ * B := by
      simpa [Finset.centerMass, smul_eq_mul, Function.comp_def, W, A, B] using hj
    have hWpow : 0 ≤ W ^ q := Real.rpow_nonneg hW0 q
    have hpowle : W ^ (q - 1) ≤ 1 := by
      calc
        W ^ (q - 1) ≤ (1 : ℝ) ^ (q - 1) :=
          Real.rpow_le_rpow hW0 (by simpa [W] using hw1) (by linarith : 0 ≤ q - 1)
        _ = 1 := by norm_num
    have hWA : W * (W⁻¹ * A) = A := by field_simp
    calc
      A ^ q = (W * (W⁻¹ * A)) ^ q := congrArg (fun x : ℝ => x ^ q) hWA.symm
      _ = W ^ q * (W⁻¹ * A) ^ q :=
        Real.mul_rpow hW0 (mul_nonneg (inv_nonneg.mpr hW0) hA0)
      _ ≤ W ^ q * (W⁻¹ * B) := mul_le_mul_of_nonneg_left hj' hWpow
      _ = W ^ (q - 1) * B := by
        rw [Real.rpow_sub hWpos q 1, Real.rpow_one]
        field_simp
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hpowle hB0
      _ = B := one_mul B

end

end RHTower

namespace ContinuousLinearMap

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H}

/-- The `q`-power diagonal of a positive Schatten operator is bounded by its singular-value
`q`-sum on every finite orthonormal-with-zeros packet. -/
theorem sum_rpow_re_inner_apply_le_tsum_approxNumber
    {ι : Type*} {q : ℝ} (hq : 1 ≤ q) (hT : 0 ≤ T)
    (hSch : MemSchattenClass q T) (g : ι → H)
    (hg : ∀ i, g i = 0 ∨ ‖g i‖ = 1)
    (hgo : ∀ i j, i ≠ j → inner ℂ (g i) (g j) = 0)
    (s : Finset ι) :
    ∑ i ∈ s, RCLike.re (inner ℂ (g i) (T (g i)) : ℂ) ^ q ≤
      ∑' k, approxNumber T k ^ q := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcpt : IsCompactOperator T := hSch.isCompactOperator hq0
  have hsvSummable : Summable fun k => singVal T k ^ q := by
    exact hSch.congr fun k => by rw [approxNumber_eq_singVal hcpt k]
  let e : ℕ → H := fun k => svVec (energyOp T) k
  let d : ι → ℝ := fun i => RCLike.re (inner ℂ (g i) (T (g i)) : ℂ)
  have hpoint : ∀ i, d i ^ q ≤
      ∑' k, singVal T k ^ q * ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 := by
    intro i
    let c : ℕ → ℝ := fun k => ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2
    have hcsum : Summable c := by
      simpa [c, e] using summable_inner_svVec_sq hcpt (g i)
    have hctsum : ∑' k, c k ≤ 1 := by
      calc
        ∑' k, c k ≤ ‖g i‖ ^ 2 := by
          simpa [c, e] using tsum_inner_svVec_sq_le hcpt (g i)
        _ ≤ 1 := by
          rcases hg i with hi | hi
          · rw [hi, norm_zero]
            norm_num
          · rw [hi]
            norm_num
    have hcle : ∀ k, c k ≤ 1 := by
      intro k
      exact (hcsum.le_tsum k (fun j _ => by dsimp [c]; positivity)).trans hctsum
    have hRsum : Summable fun k => singVal T k ^ q * c k :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (Real.rpow_nonneg (singVal_nonneg T k) q)
          (by dsimp [c]; positivity))
        (fun k => by
          calc
            singVal T k ^ q * c k ≤ singVal T k ^ q * 1 :=
              mul_le_mul_of_nonneg_left (hcle k)
                (Real.rpow_nonneg (singVal_nonneg T k) q)
            _ = singVal T k ^ q := mul_one _)
        hsvSummable
    have hs := hasSum_re_inner_apply_of_nonneg hcpt hT (g i)
    have hpartial : ∀ N : ℕ,
        (∑ k ∈ Finset.range N, singVal T k * c k) ^ q ≤
          ∑' k, singVal T k ^ q * c k := by
      intro N
      have hw1 : ∑ k ∈ Finset.range N, c k ≤ 1 :=
        (hcsum.sum_le_tsum (Finset.range N)
          (fun k _ => by dsimp [c]; positivity)).trans hctsum
      have hj := finset_weighted_sum_rpow_le_sum_weighted_rpow
        (Finset.range N) c (singVal T) hq
        (fun k _ => by dsimp [c]; positivity) (fun k _ => singVal_nonneg T k) hw1
      calc
        (∑ k ∈ Finset.range N, singVal T k * c k) ^ q =
            (∑ k ∈ Finset.range N, c k * singVal T k) ^ q := by
              congr 1
              exact Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ ≤ ∑ k ∈ Finset.range N, c k * singVal T k ^ q := hj
        _ = ∑ k ∈ Finset.range N, singVal T k ^ q * c k :=
          Finset.sum_congr rfl fun k _ => mul_comm _ _
        _ ≤ ∑' k, singVal T k ^ q * c k :=
          hRsum.sum_le_tsum (Finset.range N) (fun k _ =>
            mul_nonneg (Real.rpow_nonneg (singVal_nonneg T k) q)
              (by dsimp [c]; positivity))
    have htend : Filter.Tendsto
        (fun N => (∑ k ∈ Finset.range N, singVal T k * c k) ^ q)
        Filter.atTop (nhds (d i ^ q)) := by
      have hs' : HasSum (fun k => singVal T k * c k) (d i) := by
        simpa [c, e, d] using hs
      exact (Real.continuousAt_rpow_const (d i) q (Or.inr hq0.le)).tendsto.comp
        hs'.tendsto_sum_nat
    simpa [c] using le_of_tendsto' htend hpartial
  have hRsum : ∀ i ∈ s,
      Summable fun k => singVal T k ^ q * ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 := by
    intro i hi
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (Real.rpow_nonneg (singVal_nonneg T k) q) (by positivity))
      (fun k => ?_) hsvSummable
    have hinner : ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 ≤ 1 := by
      have hsum := summable_inner_svVec_sq hcpt (g i)
      have hsingle := hsum.le_tsum k (fun j _ => by positivity)
      calc
        _ ≤ ∑' j, ‖(inner ℂ (svVec (energyOp T) j) (g i) : ℂ)‖ ^ 2 := by
          simpa [e] using hsingle
        _ ≤ ‖g i‖ ^ 2 := tsum_inner_svVec_sq_le hcpt (g i)
        _ ≤ 1 := by rcases hg i with hi | hi <;> simp [hi]
    simpa using mul_le_mul_of_nonneg_left hinner
      (Real.rpow_nonneg (singVal_nonneg T k) q)
  have hcoeffLe : ∀ k, ∑ i ∈ s, ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 ≤ 1 := by
    intro k
    have hbessel := RHTower.sum_inner_sq_le_of_orthonormal_with_zeros g hg hgo (e k) s
    have hswap : ∀ i, ‖(inner ℂ (e k) (g i) : ℂ)‖ =
        ‖(inner ℂ (g i) (e k) : ℂ)‖ := by
      intro i
      rw [← inner_conj_symm, RCLike.norm_conj]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hswap i])]
    apply hbessel.trans
    rcases eq_or_ne (svVal (energyOp T) k) 0 with hzero | hne
    · simp [e, svVec_eq_zero_of_svVal_eq_zero _ hzero]
    · dsimp [e]
      rw [norm_svVec_of_ne_zero (energyOp_compact hcpt)
        (energyOp_symmetric T) (energyOp_pos T) hne]
      norm_num
  have hdoubleSummable : Summable fun k => ∑ i ∈ s,
      singVal T k ^ q * ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le
      (fun k => Finset.sum_nonneg fun i _ => mul_nonneg
        (Real.rpow_nonneg (singVal_nonneg T k) q) (by positivity)) ?_ hsvSummable
    intro k
    rw [← Finset.mul_sum]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (singVal_nonneg T k) q) (hcoeffLe k)
  have hmain : ∑ i ∈ s, d i ^ q ≤ ∑' k, singVal T k ^ q := by
    calc
      ∑ i ∈ s, d i ^ q ≤ ∑ i ∈ s,
          ∑' k, singVal T k ^ q * ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hpoint i
      _ = ∑' k, ∑ i ∈ s,
          singVal T k ^ q * ‖(inner ℂ (e k) (g i) : ℂ)‖ ^ 2 := by
        symm
        exact Summable.tsum_finsetSum hRsum
      _ ≤ ∑' k, singVal T k ^ q :=
        hdoubleSummable.tsum_le_tsum (fun k => by
          rw [← Finset.mul_sum]
          exact mul_le_of_le_one_right
            (Real.rpow_nonneg (singVal_nonneg T k) q) (hcoeffLe k)) hsvSummable
  rw [show (∑' k, approxNumber T k ^ q) = ∑' k, singVal T k ^ q by
    exact tsum_congr fun k => by rw [approxNumber_eq_singVal hcpt k]]
  simpa [d] using hmain

/-- Every orthonormal-with-zeros diagonal of a positive `S_q` operator is `q`-summable for
`q ≥ 1`. -/
theorem summable_rpow_re_inner_apply_of_nonneg_of_memSchattenClass
    {ι : Type*} {q : ℝ} (hq : 1 ≤ q) (hT : 0 ≤ T)
    (hSch : MemSchattenClass q T) (g : ι → H)
    (hg : ∀ i, g i = 0 ∨ ‖g i‖ = 1)
    (hgo : ∀ i j, i ≠ j → inner ℂ (g i) (g j) = 0) :
    Summable fun i => RCLike.re (inner ℂ (g i) (T (g i)) : ℂ) ^ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hcpt : IsCompactOperator T := hSch.isCompactOperator hq0
  refine summable_of_sum_le (c := ∑' k, approxNumber T k ^ q) (fun i => ?_) fun s =>
    sum_rpow_re_inner_apply_le_tsum_approxNumber hq hT hSch g hg hgo s
  have hd0 := (hasSum_re_inner_apply_of_nonneg hcpt hT (g i)).nonneg fun k =>
    mul_nonneg (singVal_nonneg T k) (sq_nonneg _)
  exact Real.rpow_nonneg hd0 q

end

end ContinuousLinearMap
