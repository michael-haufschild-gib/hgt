import GaloisForLFunctions.RHTower.WeilLogShiftLogarithmicMean
import GaloisForLFunctions.RHTower.WeilLogShiftNodalDistortion

/-! Logarithmic nodal weights have monotone distortion with a local endpoint bound. -/

open scoped BigOperators
noncomputable section
namespace RHTower

def finiteWeilLogNodalDistortion {r : ℕ} (x : Fin (r + 2) → ℝ) (i : Fin (r + 2)) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, finiteWeilLogarithmicMean (x i) (x j)

theorem finiteWeilLogNodalDistortion_pos {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (i : Fin (r + 2)) :
    0 < finiteWeilLogNodalDistortion x i := by
  apply Finset.prod_pos
  intro j hj
  exact finiteWeilLogarithmicMean_pos (hx i) (hx j)
    (fun he => Finset.ne_of_mem_erase hj (hinj he).symm)

/-- The shared logarithmic mean cancels, leaving exactly r factors. -/
theorem finiteWeilLogNodalDistortion_ratio {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (i j : Fin (r + 2)) (hij : i ≠ j) :
    finiteWeilLogNodalDistortion x j / finiteWeilLogNodalDistortion x i =
      ∏ l ∈ (Finset.univ.erase i).erase j,
        finiteWeilLogarithmicMean (x j) (x l) / finiteWeilLogarithmicMean (x i) (x l) := by
  have hi : finiteWeilLogNodalDistortion x i = finiteWeilLogarithmicMean (x i) (x j) *
      ∏ l ∈ (Finset.univ.erase i).erase j, finiteWeilLogarithmicMean (x i) (x l) :=
    (Finset.mul_prod_erase (Finset.univ.erase i)
      (fun l => finiteWeilLogarithmicMean (x i) (x l))
      (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)).symm
  have hj : finiteWeilLogNodalDistortion x j = finiteWeilLogarithmicMean (x j) (x i) *
      ∏ l ∈ (Finset.univ.erase i).erase j, finiteWeilLogarithmicMean (x j) (x l) := by
    rw [Finset.erase_right_comm]
    exact (Finset.mul_prod_erase (Finset.univ.erase j)
      (fun l => finiteWeilLogarithmicMean (x j) (x l))
      (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)).symm
  have hL := finiteWeilLogarithmicMean_pos (hx i) (hx j) (fun he => hij (hinj he))
  rw [hj, hi, finiteWeilLogarithmicMean_symm (x j) (x i),
    mul_div_mul_left _ _ hL.ne', Finset.prod_div_distrib]

/-- The product distortion is exactly the change in absolute raw nodal weights. -/
theorem finiteWeilLogNodalDistortion_weights_abs {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (i : Fin (r + 2)) :
    |finiteWeilMomentWeights (fun j => Real.log (x j)) i| =
      finiteWeilLogNodalDistortion x i * |finiteWeilMomentWeights x i| := by
  rw [finiteWeilMomentWeights_abs_product, finiteWeilMomentWeights_abs_product,
    finiteWeilLogNodalDistortion, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hne : x i ≠ x j := fun he => Finset.ne_of_mem_erase hj (hinj he).symm
  have hL := finiteWeilLogarithmicMean_pos (hx i) (hx j) hne
  have hD : 0 < |x i - x j| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlog : 0 < |Real.log (x i) - Real.log (x j)| :=
    abs_pos.mpr (sub_ne_zero.mpr (fun he => hne (Real.log_injOn_pos (hx i) (hx j) he)))
  rw [← abs_of_pos hL, finiteWeilLogarithmicMean, abs_div]
  field_simp

theorem finiteWeilLogNodalDistortion_eq_weight_ratio {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) (i : Fin (r + 2)) :
    finiteWeilLogNodalDistortion x i =
      |finiteWeilMomentWeights (fun j => Real.log (x j)) i| / |finiteWeilMomentWeights x i| := by
  have hW : 0 < |finiteWeilMomentWeights x i| :=
    abs_pos.mpr (finiteWeilMomentWeights_ne_zero x hinj i)
  rw [finiteWeilLogNodalDistortion_weights_abs x hx hinj i]
  field_simp

/-- Local distortion uses the two compared nodes, with r surviving product factors. -/
theorem finiteWeilLogNodalDistortion_local_ratio {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (i j : Fin (r + 2)) (hij : i ≠ j) (horder : x i ≤ x j) :
    1 ≤ finiteWeilLogNodalDistortion x j / finiteWeilLogNodalDistortion x i ∧
    finiteWeilLogNodalDistortion x j / finiteWeilLogNodalDistortion x i ≤ (x j / x i) ^ r := by
  let T := (Finset.univ.erase i).erase j
  have hcard : T.card = r := by
    dsimp [T]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩),
      Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have hf : ∀ l ∈ T,
      1 ≤ finiteWeilLogarithmicMean (x j) (x l) / finiteWeilLogarithmicMean (x i) (x l) ∧
      finiteWeilLogarithmicMean (x j) (x l) / finiteWeilLogarithmicMean (x i) (x l) ≤ x j / x i := by
    intro l hl
    have hli : l ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hl)
    have hlj : l ≠ j := Finset.ne_of_mem_erase hl
    have hil : x i ≠ x l := fun he => hli (hinj he).symm
    have hjl : x j ≠ x l := fun he => hlj (hinj he).symm
    have hL := finiteWeilLogarithmicMean_pos (hx i) (hx l) hil
    have hc := finiteWeilLogarithmicMean_local_comparison (hx i) (hx j) (hx l) hil hjl horder
    exact ⟨(le_div_iff₀ hL).mpr (by simpa only [one_mul] using hc.1), (div_le_iff₀ hL).mpr hc.2⟩
  rw [finiteWeilLogNodalDistortion_ratio x hx hinj i j hij]
  constructor
  · have h : (∏ _l ∈ T, (1 : ℝ)) ≤ ∏ l ∈ T,
        finiteWeilLogarithmicMean (x j) (x l) / finiteWeilLogarithmicMean (x i) (x l) :=
      Finset.prod_le_prod (fun _ _ => by norm_num) (fun l hl => (hf l hl).1)
    simpa only [Finset.prod_const, one_pow] using h
  · calc
      _ ≤ ∏ _l ∈ T, x j / x i := Finset.prod_le_prod
        (fun l hl => by linarith only [(hf l hl).1]) (fun l hl => (hf l hl).2)
      _ = _ := by rw [Finset.prod_const, hcard]

/-- Distortion is monotone in the node value, with a division-free local bound. -/
theorem finiteWeilLogNodalDistortion_local_bounds {r : ℕ} (x : Fin (r + 2) → ℝ)
    (hx : ∀ i, 0 < x i) (hinj : Function.Injective x)
    (i j : Fin (r + 2)) (hij : i ≠ j) (horder : x i ≤ x j) :
    finiteWeilLogNodalDistortion x i ≤ finiteWeilLogNodalDistortion x j ∧
    x i ^ r * finiteWeilLogNodalDistortion x j ≤ x j ^ r * finiteWeilLogNodalDistortion x i := by
  obtain ⟨hl, hu⟩ := finiteWeilLogNodalDistortion_local_ratio x hx hinj i j hij horder
  have hi := finiteWeilLogNodalDistortion_pos x hx hinj i
  refine ⟨by simpa only [one_mul] using (le_div_iff₀ hi).mp hl, ?_⟩
  have hc := (div_le_iff₀ hi).mp hu
  rw [div_pow] at hc
  have hpow : 0 < x i ^ r := pow_pos (hx i) r
  calc
    _ ≤ x i ^ r * ((x j ^ r / x i ^ r) * finiteWeilLogNodalDistortion x i) :=
      mul_le_mul_of_nonneg_left hc hpow.le
    _ = _ := by field_simp

end RHTower
