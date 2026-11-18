import GaloisForLFunctions.HTGeometry.HalfShiftHarmonicEulerBound
import GaloisForLFunctions.RHTower.FloorTransformPowerThreshold

/-! # The canonical Stirling remainder is invertible at square-root precision

The first differences of the factorial remainder are positive, start at
one, and have off-diagonal square-root mass strictly below one. A strong
induction inverts their floor transform without changing any power bound
of exponent at least one half.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset _root_.RHTower

/-- First difference of log(j!) − j log j + j at positive j. -/
def factorialStirlingStep (j : ℕ) : ℝ :=
  1+Real.log j-((j:ℝ)*Real.log j-((j-1:ℕ):ℝ)*Real.log (j-1:ℕ))

@[simp] theorem factorialStirlingStep_one : factorialStirlingStep 1=1 := by
  simp [factorialStirlingStep]

private theorem step_formula {n : ℕ} (hn : 0 < n) :
    factorialStirlingStep (n+1)=1-(n:ℝ)*Real.log (((n:ℝ)+1)/n) := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  simp only [factorialStirlingStep,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,
    Real.log_div (by positivity : (n:ℝ)+1≠0) hn'.ne']
  ring

/-- The Stirling step is a positive mixture of reciprocal integer powers.
At one the same expansion is the telescoping sum of consecutive inverses. -/
theorem hasSum_factorialStirlingStep {j : ℕ} (hj : 0 < j) :
    HasSum (fun k : ℕ => ((j:ℝ)⁻¹)^(k+1)/(((k:ℝ)+1)*((k:ℝ)+2))) (factorialStirlingStep j) := by
  rcases j with _ | n
  · omega
  rcases n with _ | n
  · simp only [Nat.zero_add,Nat.cast_one,inv_one,one_pow,factorialStirlingStep_one]
    let b := fun k : ℕ => 1/((k:ℝ)+1)
    have hf (k : ℕ) : 1/(((k:ℝ)+1)*((k:ℝ)+2)) = b k - b (k+1) := by
      dsimp only [b]
      push_cast
      field_simp <;> ring
    have h₀ : Filter.Tendsto b Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ))))
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun k => by positivity) _).mpr
    simp_rw [hf,sum_range_sub']
    simpa [b] using (tendsto_const_nhds (x := (1:ℝ))).sub h₀
  let j : ℕ := n+2
  let x : ℝ := (j:ℝ)⁻¹
  have hj₁ : (1:ℝ) < j := by exact_mod_cast (by omega : 1 < n+2)
  have hj₀ := zero_lt_one.trans hj₁
  have hx : 0 < x := inv_pos.mpr hj₀
  have hx' : x < 1 := inv_lt_one_of_one_lt₀ hj₁
  let A := fun k : ℕ => x^(k+1)/((k:ℝ)+1)
  let L := -Real.log (1-x)
  have hA : HasSum A L := Real.hasSum_pow_div_log_of_abs_lt_one (by rw [abs_of_pos hx]; exact hx')
  have ht : HasSum (fun k => A (k+1)) (L-x) := by
    have h := (hasSum_nat_add_iff' 1).mpr hA
    simpa only [A,range_one,sum_singleton,Nat.cast_zero,zero_add,pow_one,div_one] using h
  have he (k : ℕ) : A k - A (k+1)/x = x^(k+1)/(((k:ℝ)+1)*((k:ℝ)+2)) := by
    dsimp only [A]
    push_cast
    rw [pow_succ x (k+1)]
    field_simp [hx.ne'] <;> ring
  have h := (hA.sub (ht.div_const x)).congr_fun (fun k => (he k).symm)
  have hfrac : 1-x = ((n:ℝ)+1)/((n:ℝ)+2) := by
    dsimp only [x,j]; push_cast; field_simp <;> ring
  have hL : L = Real.log (((n:ℝ)+2)/((n:ℝ)+1)) := by
    rw [show L = -Real.log (1-x) from rfl,hfrac,← Real.log_inv,inv_div]
  have hvalue : factorialStirlingStep (n+1+1) = L - (L-x)/x := by
    rw [step_formula (by omega : 0 < n+1)]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [show (n:ℝ)+1+1=n+2 by ring,hL]
    dsimp only [x,j]; push_cast; field_simp <;> ring
  rw [hvalue]
  exact h

private theorem step_bounds {n : ℕ} (hn : 0 < n) :
    0 ≤ factorialStirlingStep (n+1) ∧ factorialStirlingStep (n+1) ≤ 1/(2*(n:ℝ)+1) := by
  have hx : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  let r := ((n:ℝ)+1)/n
  have hr : 1 ≤ r := (one_le_div hx).mpr (by linarith)
  have hr₀ := zero_lt_one.trans_le hr
  have hupper := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hr₀) hx.le
  have hlower := mul_le_mul_of_nonneg_left (HTGeometry.two_mul_sub_one_div_add_one_le_log hr) hx.le
  have he : (n:ℝ)*(r-1)=1 := by dsimp only [r]; field_simp <;> ring
  have hf : (n:ℝ)*(2*(r-1)/(r+1))=1-1/(2*(n:ℝ)+1) := by
    dsimp only [r]
    field_simp <;> ring
  rw [he] at hupper
  rw [hf] at hlower
  rw [step_formula hn]
  exact ⟨sub_nonneg.mpr hupper,by change 1-(n:ℝ)*Real.log r ≤ _; linarith only [hlower]⟩

/-- Each nonidentity weight fits strictly under the difference of two
successive inverse square roots. -/
theorem factorialStirlingStep_sqrt_gap {n : ℕ} (hn : 0 < n) :
    factorialStirlingStep (n+1)/Real.sqrt ((n:ℝ)+1) <
      1/Real.sqrt (n:ℝ)-1/Real.sqrt ((n:ℝ)+1) := by
  have hx : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hp := (step_bounds hn).2
  have hden : 0 < 2*(n:ℝ)+1 := by positivity
  have hsq : (Real.sqrt n*(1+1/(2*(n:ℝ)+1)))^2 < (Real.sqrt ((n:ℝ)+1))^2 := by
    rw [mul_pow,Real.sq_sqrt hx.le,Real.sq_sqrt (by positivity)]
    field_simp <;> nlinarith only [hx]
  have hroot := (sq_lt_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsq
  have hmul := mul_le_mul_of_nonneg_left (add_le_add_left hp 1) (Real.sqrt_nonneg n)
  rw [lt_sub_iff_add_lt,← add_div,div_lt_div_iff₀ (Real.sqrt_pos.mpr (by positivity)) (Real.sqrt_pos.mpr hx)]
  linarith only [hmul,hroot]

/-- The same contraction constant works at every finite cutoff. -/
theorem factorialStirlingStep_tail_mass : ∃ K : ℝ, 0 ≤ K ∧ K < 1 ∧ ∀ N : ℕ,
    ∑ j ∈ Icc 2 N, factorialStirlingStep j/Real.sqrt j ≤ K := by
  let K := (factorialStirlingStep 2+1)/Real.sqrt 2
  have h₂ : 0 ≤ factorialStirlingStep 2 := (step_bounds (n := 1) Nat.one_pos).1
  have hgap := factorialStirlingStep_sqrt_gap (n := 1) Nat.one_pos
  norm_num only [Nat.cast_one,Real.sqrt_one,div_one,one_add_one_eq_two] at hgap
  have hsplit : K=factorialStirlingStep 2/Real.sqrt 2+1/Real.sqrt 2 := add_div _ _ _
  have hK : K < 1 := by rw [hsplit]; linarith only [hgap]
  refine ⟨K,div_nonneg (by linarith only [h₂]) (Real.sqrt_nonneg _),hK,fun N => ?_⟩
  by_cases hN : 2 ≤ N
  · have aux : ∑ j ∈ Icc 2 N, factorialStirlingStep j/Real.sqrt j ≤ K-1/Real.sqrt N := by
      induction N, hN using Nat.le_induction with
      | base => simp only [Icc_self,sum_singleton,Nat.cast_ofNat,hsplit]; linarith
      | succ n hn ih =>
        rw [sum_Icc_succ_top (by omega)]
        have h := factorialStirlingStep_sqrt_gap (n := n) (by omega)
        simp only [Nat.cast_add,Nat.cast_one]
        linarith only [ih,h]
    exact aux.trans (sub_le_self _ (by positivity))
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hN),sum_empty]
    exact div_nonneg (by linarith only [h₂]) (Real.sqrt_nonneg _)

private theorem step_nonneg {j : ℕ} (hj : 2 ≤ j) : 0 ≤ factorialStirlingStep j := by
  cases j with
  | zero => omega
  | succ j => exact (step_bounds (by omega : 0 < j)).1

/-- The Dirichlet series of the Stirling steps stays uniformly away from zero
on the closed half-plane of square-root precision. The tail starts at two. -/
theorem factorialStirlingStep_dirichlet_lower :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℂ, 1/2 ≤ s.re →
      let term := fun n : ℕ => (factorialStirlingStep (n+2) : ℂ) *
        Complex.exp (-(Real.log (n+2:ℕ) : ℂ)*s)
      Summable term ∧ δ ≤ ‖1 + ∑' n, term n‖ := by
  obtain ⟨K,_,hK,hcut⟩ := factorialStirlingStep_tail_mass
  refine ⟨1-K,sub_pos.mpr hK,fun s hs => ?_⟩
  let b := fun n : ℕ => factorialStirlingStep (n+2) / Real.sqrt (n+2:ℕ)
  let f := fun n : ℕ => (factorialStirlingStep (n+2) : ℂ) *
    Complex.exp (-(Real.log (n+2:ℕ) : ℂ)*s)
  have hsum (N : ℕ) : ∑ n ∈ range N, b n =
      ∑ j ∈ Icc 2 (N+1), factorialStirlingStep j / Real.sqrt j := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ,ih]
      conv_rhs => rw [sum_Icc_succ_top (show 2 ≤ N+1+1 by omega)]
  have hb (n : ℕ) : 0 ≤ b n := div_nonneg (step_nonneg (by omega)) (Real.sqrt_nonneg _)
  have hbound (N : ℕ) : ∑ n ∈ range N, b n ≤ K := (hsum N).trans_le (hcut _)
  have hnorm (n : ℕ) : ‖f n‖ ≤ b n := by
    let j := n+2
    have hj : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast (by omega : 1 ≤ n+2)
    have hj' := zero_lt_one.trans_le hj
    change ‖(factorialStirlingStep j : ℂ)*Complex.exp (-(Real.log j : ℂ)*s)‖ ≤
      factorialStirlingStep j / Real.sqrt j
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (step_nonneg (by omega : 2 ≤ j)),
      Complex.norm_exp,← Complex.ofReal_neg,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,neg_mul,Real.exp_neg,← Real.rpow_def_of_pos hj',← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left (step_nonneg (by omega)) (Real.sqrt_pos.mpr hj')
      ((Real.sqrt_eq_rpow _).trans_le (Real.rpow_le_rpow_of_exponent_le hj hs))
  have hbSum := summable_of_sum_range_le hb hbound
  have hf : Summable (fun n => ‖f n‖) := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hnorm hbSum
  have ht : ‖∑' n, f n‖ ≤ K := (norm_tsum_le_tsum_norm hf).trans
    ((hf.tsum_le_tsum hnorm hbSum).trans (Real.tsum_le_of_sum_range_le hb hbound))
  have hl := norm_sub_norm_le (1:ℂ) (-(∑' n, f n))
  rw [norm_one,norm_neg,sub_neg_eq_add] at hl
  exact ⟨hf.of_norm,by linarith only [ht,hl]⟩

private theorem transform_tail {F : ℕ → ℝ} {N : ℕ} {s A K : ℝ} (hs : 1/2 ≤ s)
    (hA : 0 ≤ A) (hF : ∀ k, 0 < k → k < N → |F k| ≤ A*(k:ℝ)^s)
    (hK : ∑ j ∈ Icc 2 N, factorialStirlingStep j/Real.sqrt j ≤ K) :
    |∑ j ∈ Icc 2 N, factorialStirlingStep j*F (N/j)| ≤ A*(N:ℝ)^s*K := by
  have hs₀ : 0 ≤ s := by linarith only [hs]
  have haux {j : ℕ} (hj : j ∈ Icc 2 N) :
      |factorialStirlingStep j*F (N/j)| ≤ A*(N:ℝ)^s*(factorialStirlingStep j/Real.sqrt j) := by
    obtain ⟨hj₂,hjN⟩ := mem_Icc.mp hj
    have hj₁ : (1:ℝ) ≤ j := by exact_mod_cast (by omega : 1 ≤ j)
    have hj₀ := zero_lt_one.trans_le hj₁
    have hval := hF (N/j) (Nat.div_pos hjN (by omega)) (Nat.div_lt_self (by omega) (by omega))
    have hcast : ((N/j:ℕ):ℝ) ≤ (N:ℝ)/j := Nat.cast_div_le
    have hp := Real.rpow_le_rpow (Nat.cast_nonneg (N/j)) hcast hs₀
    rw [Real.div_rpow (Nat.cast_nonneg _) hj₀.le] at hp
    have ht := (Real.sqrt_eq_rpow j).trans_le (Real.rpow_le_rpow_of_exponent_le hj₁ hs)
    have hb := (hval.trans (mul_le_mul_of_nonneg_left hp hA)).trans
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.sqrt_pos.mpr hj₀) ht) hA)
    rw [abs_mul,abs_of_nonneg (step_nonneg hj₂)]
    exact (mul_le_mul_of_nonneg_left hb (step_nonneg hj₂)).trans_eq (by ring)
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun _ hj => haux hj).trans
    (by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hK (mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _))))

private theorem transform_split (F : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    floorTransform factorialStirlingStep F n = F n+
      ∑ j ∈ Icc 2 n, factorialStirlingStep j*F (n/j) := by
  have hsplit : Icc 1 n = insert 1 (Icc 2 n) := by
    ext j
    simp only [mem_Icc,mem_insert]
    omega
  rw [floorTransform,hsplit,sum_insert (by simp),factorialStirlingStep_one,Nat.div_one,one_mul]

/-- A power bound for the canonical floor transform is equivalent to the
same power bound for its input, including the exact square-root endpoint. -/
theorem factorialStirlingStep_power_bound_iff (F : ℕ → ℝ) {s : ℝ} (hs : 1/2 ≤ s) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → |floorTransform factorialStirlingStep F n| ≤ C*(n:ℝ)^s) ↔
    (∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → |F n| ≤ C*(n:ℝ)^s) := by
  obtain ⟨K,hK,hK₁,hmass⟩ := factorialStirlingStep_tail_mass
  constructor
  · rintro ⟨C,hC,h⟩
    let A := C/(1-K)
    have hpos := sub_pos.mpr hK₁
    have hA : 0 ≤ A := div_nonneg hC hpos.le
    have he : A*(1-K)=C := div_mul_cancel₀ _ hpos.ne'
    refine ⟨A,hA,fun n => ?_⟩
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have ht := transform_tail hs hA (fun j hj hjn => ih j hjn hj) (hmass n)
      have hf := h n hn
      have hh := abs_sub (floorTransform factorialStirlingStep F n) (∑ j ∈ Icc 2 n, factorialStirlingStep j*F (n/j))
      rw [transform_split F hn,add_sub_cancel_right] at hh
      rw [transform_split F hn] at hf
      have he' := congrArg (fun z : ℝ => z*(n:ℝ)^s) he
      linarith only [hh,ht,hf,he']
  · rintro ⟨C,hC,h⟩
    refine ⟨C*(1+K),by positivity,fun n hn => ?_⟩
    rw [transform_split F hn]
    have ht := transform_tail hs hC (fun j hj _ => h j hj) (hmass n)
    exact (abs_add_le _ _).trans ((add_le_add (h n hn) ht).trans_eq (by ring))

end GaloisForLFunctions.CountingHolography.Sections
