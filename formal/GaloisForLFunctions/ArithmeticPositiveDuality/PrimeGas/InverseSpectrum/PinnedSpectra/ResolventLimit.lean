import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Resolvent

/-! # Resolvent product limits for every interlacing spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology Finset

theorem mixture_stieltjes_bounds {m : ℕ} (b : PrefixData m) {x : ℝ} (hx : 0 < x) :
    prefixProduct b x/(x+occupationWeight m) ≤ ∑' n, prefixProbability b n/(x+occupationWeight n) ∧
    (∑' n, prefixProbability b n/(x+occupationWeight n)) ≤ prefixProduct b x/x := by
  let f (k : ℕ) := tailLaw k/(x+occupationWeight (m+k))
  have hpos (k : ℕ) := add_pos hx (occupationWeight_pos (m+k))
  have hu (k : ℕ) : f k ≤ tailLaw k/x := div_le_div_of_nonneg_left (tailLaw_pos _).le hx (le_add_of_nonneg_right (occupationWeight_pos _).le)
  have hl (k : ℕ) : tailLaw k/(x+occupationWeight m) ≤ f k :=
    div_le_div_of_nonneg_left (tailLaw_pos _).le (hpos _) (add_le_add_right (occupationWeight_antitone (Nat.le_add_right m k)) _)
  have hs : Summable f := (tailLaw_sum.summable.div_const x).of_nonneg_of_le (fun k => div_nonneg (tailLaw_pos _).le (hpos _).le) hu
  have hlow := (tailLaw_sum.summable.div_const (x+occupationWeight m)).tsum_le_tsum hl hs
  have hhigh := hs.tsum_le_tsum hu (tailLaw_sum.summable.div_const x)
  rw [tsum_div_const,tailLaw_sum.tsum_eq] at hlow hhigh
  rw [mixture_stieltjes b hx]
  have hin := (prefixProduct_pos b hx).le
  simpa only [div_eq_mul_inv,one_mul,f] using
    And.intro (mul_le_mul_of_nonneg_left hlow hin) (mul_le_mul_of_nonneg_left hhigh hin)

def bandProduct (b : SpectralBand 1) (x : ℝ) (m : ℕ) :=
  ∏ k ∈ range m, (x+(b k).val)/(x+occupationWeight k)

private theorem product_restrict (b : SpectralBand 1) (x : ℝ) (m : ℕ) :
    prefixProduct (fun j : Fin m => b j.val) x = bandProduct b x m := Fin.prod_univ_eq_prod_range _ _

private theorem product_positive (b : SpectralBand 1) {x : ℝ} (hx : 0 < x) (m : ℕ) : 0 < bandProduct b x m :=
  (prefixProduct_pos (fun j : Fin m => b j.val) hx).trans_eq (product_restrict b x m)

/-- The cold interlacing endpoints give a telescoping lower bound for every finite characteristic product. -/
theorem bandProduct_cold_lower (b : SpectralBand 1) {x : ℝ} (hx : 0 < x) (m : ℕ) :
    (x+occupationWeight m)/(x+1) ≤ bandProduct b x m := by
  have h1 := add_pos hx zero_lt_one
  induction m with
  | zero =>
    simp only [bandProduct,prod_range_zero,occupationWeight_zero,div_self h1.ne',le_refl]
  | succ m ih =>
    have hd := add_pos hx (occupationWeight_pos m)
    have hn := add_pos hx (occupationWeight_pos (m+1))
    rw [show bandProduct b x (m+1) = bandProduct b x m*((x+(b m).val)/(x+occupationWeight m)) from prod_range_succ _ _]
    calc (x+occupationWeight (m+1))/(x+1) =
          ((x+occupationWeight m)/(x+1))*((x+occupationWeight (m+1))/(x+occupationWeight m)) := by
            field_simp [h1.ne',hd.ne'] <;> ring
         _ ≤ _ := mul_le_mul ih (div_le_div_of_nonneg_right (add_le_add_right (b m).property.1 x) hd.le)
           (div_nonneg hn.le hd.le) (product_positive b hx m).le

/-- Even the infinite product stays strictly positive at every positive resolvent parameter. -/
theorem bandProduct_limit_bounds (b : SpectralBand 1) {x : ℝ} (hx : 0 < x) :
    x/(x+1) ≤ (⨅ m, bandProduct b x m) ∧ (⨅ m, bandProduct b x m) ≤ 1 := by
  constructor
  · exact le_ciInf fun m => (div_le_div_of_nonneg_right (le_add_of_nonneg_right (occupationWeight_pos m).le)
      (add_pos hx zero_lt_one).le).trans (bandProduct_cold_lower b hx m)
  · have hb : BddBelow (range (bandProduct b x)) := ⟨0,fun _ ⟨m,hm⟩ => (product_positive b hx m).le.trans_eq hm⟩
    simpa only [bandProduct,prod_range_zero] using ciInf_le hb 0

theorem bandProduct_antitone (b : SpectralBand 1) {x : ℝ} (hx : 0 < x) : Antitone (bandProduct b x) := by
  apply antitone_nat_of_succ_le
  intro m
  rw [bandProduct,prod_range_succ]
  exact mul_le_of_le_one_right (product_positive b hx m).le
    ((div_le_one (add_pos hx (occupationWeight_pos _))).mpr (add_le_add_right (b m).property.2 _))

/-- The limit of the section's resolvent readings is the infimum of the native finite spectral products. -/
theorem prefix_stieltjes_tendsto (b : SpectralBand 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun m : ℕ => x*∑' n, prefixProbability (fun j : Fin m => b j.val) n/(x+occupationWeight n)) atTop
      (𝓝 (⨅ m, bandProduct b x m)) := by
  let L := ⨅ m, bandProduct b x m
  have hp : Tendsto (bandProduct b x) atTop (𝓝 L) :=
    tendsto_atTop_ciInf (bandProduct_antitone b hx) ⟨0,fun _ ⟨m,hm⟩ => (product_positive b hx m).le.trans_eq hm⟩
  have hl := (hp.div (occupationWeight_tendsto.const_add x) (by simpa only [add_zero] using hx.ne')).const_mul x
  have hu := (hp.div_const x).const_mul x
  have hval : x*(L/x)=L := by field_simp [hx.ne']
  rw [add_zero,hval] at hl
  rw [hval] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
  · intro m
    simpa only [← product_restrict b x m] using mul_le_mul_of_nonneg_left (mixture_stieltjes_bounds (fun j : Fin m => b j.val) hx).1 hx.le
  · intro m
    simpa only [← product_restrict b x m] using mul_le_mul_of_nonneg_left (mixture_stieltjes_bounds (fun j : Fin m => b j.val) hx).2 hx.le

#print axioms mixture_stieltjes_bounds
#print axioms bandProduct_cold_lower
#print axioms bandProduct_limit_bounds
#print axioms bandProduct_antitone
#print axioms prefix_stieltjes_tendsto

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
