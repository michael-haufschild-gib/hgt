import GaloisForLFunctions.ExceptionalLayerTheory.UniformTailsOfShortDirichletPolynomials
import GaloisForLFunctions.ExceptionalLayerTheory.TheAlternatingPrimeSymbolsAtARightZero
import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels
import GaloisForLFunctions.RHTower.Sieve.PerronFiniteSum
import GaloisForLFunctions.RHTower.XiHeatCassiniLogMeshLaplaceContinuation

/-!
# A finite prime wave at an arbitrary right zero

The first surviving derivative of the alternating prime symbol extracts
one frequency. Subtracting the value at each entering divisor makes the
finite kernel continuous in the cutoff. Its increments are controlled by
the same Cauchy estimate as the wave.
-/

noncomputable section

open Complex Filter Finset Topology ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

open HeckeLFunctions

/-- Frequency derivative of a dilation, centered to vanish where a divisor enters. -/
def centeredDirichletTest (k : ℕ) (ρ : ℂ) (v : ℝ) :=
  iteratedDeriv k (fun s : ℂ => (v:ℂ)^s-1) ρ

private theorem centered_one (k : ℕ) (ρ : ℂ) : centeredDirichletTest k ρ 1 = 0 := by
  simp [centeredDirichletTest]

private abbrev rowMass (a : ArithmeticFunction ℝ) (n : ℕ) :=
  ∑ d ∈ Icc 1 n, alternatingRowCoeffs a d

private abbrev scaledHead (a : ArithmeticFunction ℝ) (n : ℕ) (x : ℝ) (s : ℂ) :=
  (x:ℂ)^s * shortDirichletPrefix (alternatingRowCoeffs a) n s

private theorem power_entire {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (fun s : ℂ => (x:ℂ)^s) :=
  differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))

private theorem head_entire (a : ArithmeticFunction ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (scaledHead a n x) :=
  (power_entire hx).mul (differentiable_shortDirichletPrefix _ _)

private theorem centered_head_eq (a : ArithmeticFunction ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (fun s : ℂ => ∑ d ∈ Icc 1 n, (a d : ℂ)*(((x/d:ℝ):ℂ)^s-1)) =
      fun s => scaledHead a n x s - rowMass a n := by
  funext s
  rw [scaledHead,shortDirichletPrefix, sum_range_succ_eq_sum_Icc (by simp : LSeries.term (alternatingRowCoeffs a) s 0 = 0),
    mul_sum,rowMass,← sum_sub_distrib]
  refine sum_congr rfl fun d hd => ?_
  have hpos : (0:ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
  rw [_root_.RHTower.Sieve.ofReal_div_cpow_eq_mul_cpow_neg hx hpos,
    LSeries.term_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hd).1),Complex.cpow_neg,div_eq_mul_inv]
  simp only [Complex.ofReal_natCast,alternatingRowCoeffs]
  ring

private theorem kernel_fixed_jet (a : ArithmeticFunction ℝ) (k : ℕ) (ρ : ℂ) (n : ℕ)
    {x : ℝ} (hx : 0 < x) :
    (∑ d ∈ Icc 1 n, a d • centeredDirichletTest k ρ (x/d)) =
      iteratedDeriv k (fun s => scaledHead a n x s - rowMass a n) ρ := by
  have han (d : ℕ) (hd : d ∈ Icc 1 n) :
      AnalyticAt ℂ (fun s : ℂ => ((x/d:ℝ):ℂ)^s - 1) ρ :=
    ((power_entire (div_pos hx (by exact_mod_cast (mem_Icc.mp hd).1))).analyticAt ρ).sub analyticAt_const
  rw [← centered_head_eq a n hx,iteratedDeriv_fun_sum (n := k)
    (f := fun d (s : ℂ) => (a d : ℂ) * (((x/d:ℝ):ℂ)^s - 1)) (fun d hd =>
    (analyticAt_const.mul (han d hd)).contDiffAt)]
  refine sum_congr rfl fun d hd => ?_
  rw [iteratedDeriv_const_mul _ (han d hd).contDiffAt]
  exact Complex.real_smul

private theorem tested_head_deriv (a : ArithmeticFunction ℝ) (n k : ℕ) {θ x : ℝ}
    (hx : 0 < x) {ρ : ℂ} (hD : AnalyticAt ℂ (growthCont (alternatingRowCoeffs a) θ) ρ)
    (f : ℂ → ℂ) (hf : AnalyticAt ℂ f ρ) :
    iteratedDeriv k (fun s => f s * scaledHead a n x s) ρ =
      iteratedDeriv k (fun s => (f s * (x:ℂ)^s) * growthCont (alternatingRowCoeffs a) θ s) ρ -
      iteratedDeriv k (fun s => f s * ((x:ℂ)^s * (growthCont (alternatingRowCoeffs a) θ s -
        shortDirichletPrefix (alternatingRowCoeffs a) n s))) ρ := by
  have hp := (power_entire hx).analyticAt ρ
  rw [← iteratedDeriv_fun_sub (n := k)
    (f := fun s => (f s * (x:ℂ)^s) * growthCont (alternatingRowCoeffs a) θ s)
    (g := fun s => f s * ((x:ℂ)^s * (growthCont (alternatingRowCoeffs a) θ s -
      shortDirichletPrefix (alternatingRowCoeffs a) n s))) ((hf.mul hp).mul hD).contDiffAt
    (hf.mul (hp.mul (hD.sub ((differentiable_shortDirichletPrefix _ _).analyticAt ρ)))).contDiffAt]
  apply congrArg (fun h : ℂ → ℂ => iteratedDeriv k h ρ)
  funext s
  dsimp only [scaledHead]
  ring

private theorem change_cutoff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    (y:ℂ)^s = ((y/x:ℝ):ℂ)^s * (x:ℂ)^s := by
  rw [_root_.RHTower.Sieve.ofReal_div_cpow_eq_mul_cpow_neg hy hx,Complex.cpow_neg,mul_assoc,
    inv_mul_cancel₀ (Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))),mul_one]

/-- On one closed unit cell the centered increment is a single tested Dirichlet polynomial. -/
private theorem kernel_cell_jet (a : ArithmeticFunction ℝ) (k : ℕ) (ρ : ℂ) {n : ℕ}
    (hn : 1 ≤ n) {x y : ℝ} (hx : (n:ℝ) ≤ x) (hxy : x ≤ y) (hy : y ≤ (n:ℝ)+1) :
    arithmeticKernel a (centeredDirichletTest k ρ) y -
      arithmeticKernel a (centeredDirichletTest k ρ) x =
    iteratedDeriv k (fun s => (((y/x:ℝ):ℂ)^s - 1) * scaledHead a n x s) ρ := by
  have hx0 : 0 < x := (show 0 < (n:ℝ) by exact_mod_cast hn).trans_le hx
  have hy0 := hx0.trans_le hxy
  rw [arithmeticKernel_on_unit_interval a _ (centered_one k ρ) (hx.trans hxy) hy,
    arithmeticKernel_on_unit_interval a _ (centered_one k ρ) hx (hxy.trans hy),
    kernel_fixed_jet _ _ _ _ hy0,kernel_fixed_jet _ _ _ _ hx0,
    ← iteratedDeriv_fun_sub (n := k)
      (f := fun s => scaledHead a n y s - rowMass a n)
      (g := fun s => scaledHead a n x s - rowMass a n)
      (((head_entire a n hy0).analyticAt ρ).sub analyticAt_const).contDiffAt
      (((head_entire a n hx0).analyticAt ρ).sub analyticAt_const).contDiffAt]
  apply congrArg (fun h : ℂ → ℂ => iteratedDeriv k h ρ)
  funext s
  dsimp only [scaledHead]
  rw [change_cutoff hx0 hy0 s]
  ring

private theorem norm_cutoff_test {x y R : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hy : y ≤ x+1)
    {s : ℂ} (hs : ‖s‖ ≤ R) :
    ‖((y/x:ℝ):ℂ)^s - 1‖ ≤ (R*Real.exp R)*(Real.log y - Real.log x) := by
  have hx0 := zero_lt_one.trans_le hx
  have hy0 := hx0.trans_le hxy
  have hdiv := div_pos hy0 hx0
  let L := Real.log y - Real.log x
  have hL0 : 0 ≤ L := sub_nonneg.mpr (Real.log_le_log hx0 hxy)
  have hL1 : L ≤ 1 := by
    have he := Real.log_le_sub_one_of_pos hdiv
    rw [Real.log_div hy0.ne' hx0.ne'] at he
    have h2 : y/x ≤ 2 := (div_le_iff₀ hx0).mpr (by linarith only [hx,hy])
    dsimp only [L]
    linarith only [he,h2]
  have hn : ‖(L:ℂ)*s‖ = L*‖s‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL0]
  have hb : L*‖s‖ ≤ R := (mul_le_of_le_one_left (norm_nonneg _) hL1).trans hs
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hdiv.ne'),← Complex.ofReal_log hdiv.le,
    Real.log_div hy0.ne' hx0.ne']
  apply (_root_.RHTower.norm_exp_sub_one_le_norm_mul_exp _).trans
  change ‖(L:ℂ)*s‖ * Real.exp ‖(L:ℂ)*s‖ ≤ (R*Real.exp R)*L
  rw [hn]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hs hL0) (Real.exp_le_exp.mpr hb)
    (Real.exp_pos _).le (mul_nonneg hL0 ((norm_nonneg s).trans hs))).trans_eq (by ring)

/-- Each right zero, even in the presence of other right zeros, supplies a finite kernel
with bounded logarithmic increments and a prime convolution of amplitude `d x^ρ`. -/
theorem exists_alternating_prime_kernel_at_zero {ρ : ℂ} (hhalf : 1/2 < ρ.re)
    (hone : ρ.re < 1) (hz : riemannZeta ρ = 0) :
    ∃ (k : ℕ) (d : ℂ) (C : ℝ), d ≠ 0 ∧ 0 ≤ C ∧
      (∀ x y : ℝ, 1 ≤ x → x ≤ y →
        ‖arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ) y -
          arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ) x‖ ≤
          C*(Real.log y-Real.log x)) ∧
      ∀ x : ℝ, 1 ≤ x →
        ‖arithmeticKernel alternatingPrimeExcess (centeredDirichletTest k ρ) x -
          (x:ℂ)^ρ*d‖ ≤ C * Real.sqrt x := by
  obtain ⟨k,d,hd,hjet⟩ := alternatingSymbols_first_surviving_derivative hhalf hone hz
  let B := 75+2*|Real.eulerMascheroniConstant|
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let r := (ρ.re-1/2)/2
  have hr : 0 < r := by dsimp only [r]; linarith only [hhalf]
  have hgap : 1/2+r < ρ.re := by dsimp only [r]; linarith only [hhalf]
  let R := ‖ρ‖+r
  have hR : 0 ≤ R := add_nonneg (norm_nonneg _) hr.le
  have hcircle {s : ℂ} (hs : s ∈ Metric.sphere ρ r) : ‖s‖ ≤ R := by
    have hd := Metric.mem_closedBall.mp (Metric.sphere_subset_closedBall hs)
    rw [dist_eq_norm] at hd
    exact (norm_le_norm_add_norm_sub' s ρ).trans (add_le_add le_rfl hd)
  have hca : alternatingRowCoeffs alternatingDivisorCoeff 0 = 0 := by simp [alternatingRowCoeffs]
  have hcb : alternatingRowCoeffs alternatingPrimeExcess 0 = 0 := by simp [alternatingRowCoeffs]
  have ha := fun x hx => (alternatingRow_growth x hx).1
  have hb := fun x hx => (alternatingRow_growth x hx).2
  have hopen (t : ℝ) : IsOpen {s : ℂ | t < s.re} := isOpen_lt continuous_const continuous_re
  have hDa : AnalyticAt ℂ paritySymbol ρ :=
    (differentiableOn_growthCont hca (le_refl 0) ha).analyticOnNhd (hopen 0) ρ
      (by change 0 < ρ.re; linarith only [hhalf])
  have hDb : AnalyticAt ℂ parityPrimeSymbol ρ :=
    (differentiableOn_growthCont hcb (by norm_num : (0:ℝ) ≤ 1/2) hb).analyticOnNhd (hopen _) ρ hhalf
  obtain ⟨A,hA,hTa⟩ := exists_bound_tested_dirichlet_tail_deriv (ρ := ρ) hca (le_refl 0) zero_le_one ha
    hr (by linarith only [hgap]) k
  obtain ⟨F,hF,hTb⟩ := exists_bound_tested_dirichlet_tail_deriv hcb (by norm_num : (0:ℝ) ≤ 1/2)
    hB hb hr hgap k
  let L := A*(R*Real.exp R)
  have hL : 0 ≤ L := mul_nonneg hA (mul_nonneg hR (Real.exp_pos _).le)
  refine ⟨k,d,max L (F+B),hd,hL.trans (le_max_left ..),?_,?_⟩
  · intro x y hx hxy
    apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_left L (F+B))
      (sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le hx) hxy)))
    apply of_adjacent_unit_intervals (P := fun u v =>
      ‖arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ) v -
        arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ) u‖ ≤
        L*(Real.log v-Real.log u)) _ _ hx hxy
    · intro n hn u v hnu huv hvn
      rcases huv.lt_or_eq with huv | rfl
      · have hu1 := (show (1:ℝ) ≤ n by exact_mod_cast hn).trans hnu
        have hu := zero_lt_one.trans_le hu1
        have hv := hu.trans huv
        have hfl : ⌊u⌋₊ = n := (Nat.floor_eq_iff hu.le).mpr ⟨hnu,huv.trans_le hvn⟩
        let f := fun s : ℂ => ((v/u:ℝ):ℂ)^s-1
        have hf : Differentiable ℂ f := (power_entire (div_pos hv hu)).sub (differentiable_const _)
        have hkill := (hjet (fun s => f s * (u:ℂ)^s)
          ((hf.mul (power_entire hu)).analyticAt ρ)).1
        have hlog := sub_nonneg.mpr (Real.log_le_log hu huv.le)
        have he := hTa f hf ((R*Real.exp R)*(Real.log v-Real.log u))
          (mul_nonneg (mul_nonneg hR (Real.exp_pos _).le) hlog)
          (fun s hs => norm_cutoff_test hu1 huv.le (by linarith only [hnu,hvn]) (hcircle hs)) u hu1
        rw [hfl,Real.rpow_zero,mul_one,← mul_assoc] at he
        rw [kernel_cell_jet _ _ _ hn hnu huv.le hvn]
        change ‖iteratedDeriv k (fun s => f s * scaledHead alternatingDivisorCoeff n u s) ρ‖ ≤ _
        rw [tested_head_deriv _ _ _ hu hDa f (hf.analyticAt ρ)]
        change ‖iteratedDeriv k (fun s => (f s * (u:ℂ)^s) * paritySymbol s) ρ - _‖ ≤ _
        rw [hkill,zero_sub,norm_neg]
        exact he
      · simp
    · intro u v z huv hvz
      let K := arithmeticKernel alternatingDivisorCoeff (centeredDirichletTest k ρ)
      have htri := dist_triangle (K z) (K v) (K u)
      simp only [dist_eq_norm] at htri
      exact htri.trans ((add_le_add hvz huv).trans_eq (by ring))
  · intro x hx
    have hx0 := zero_lt_one.trans_le hx
    let a := alternatingPrimeExcess
    let n := ⌊x⌋₊
    let tail := fun s : ℂ => (x:ℂ)^s * (parityPrimeSymbol s - shortDirichletPrefix (alternatingRowCoeffs a) n s)
    let M := rowMass a n
    have hmass : ‖iteratedDeriv k (fun _ : ℂ => M) ρ‖ ≤ B*x^(1/2:ℝ) := by
      cases k with
      | zero => simpa only [iteratedDeriv_zero] using hb x hx
      | succ j =>
        rw [iteratedDeriv_const,if_neg (Nat.succ_ne_zero j),norm_zero]
        exact mul_nonneg hB (Real.rpow_nonneg hx0.le _)
    have ht : ‖iteratedDeriv k tail ρ‖ ≤ F*x^(1/2:ℝ) := by
      simpa only [tail,a,n,parityPrimeSymbol,one_mul,mul_one] using hTb (fun _ => 1) (differentiable_const _) 1 zero_le_one
        (fun _ _ => norm_one.le) x hx
    have he := tested_head_deriv a n k hx0 hDb (fun _ => 1) analyticAt_const
    simp only [one_mul] at he
    have hmain := (hjet (fun s => (x:ℂ)^s) ((power_entire hx0).analyticAt ρ)).2
    rw [arithmeticKernel,kernel_fixed_jet _ _ _ _ hx0,
      iteratedDeriv_fun_sub (f := scaledHead a n x) (g := fun _ => M)
        ((head_entire a n hx0).analyticAt ρ).contDiffAt analyticAt_const.contDiffAt,he]
    change ‖iteratedDeriv k (fun s => (x:ℂ)^s * parityPrimeSymbol s) ρ -
      iteratedDeriv k tail ρ - iteratedDeriv k (fun _ : ℂ => M) ρ - (x:ℂ)^ρ*d‖ ≤ _
    rw [hmain]
    rw [show (x:ℂ)^ρ*d - iteratedDeriv k tail ρ - iteratedDeriv k (fun _ : ℂ => M) ρ -
      (x:ℂ)^ρ*d = -(iteratedDeriv k tail ρ + iteratedDeriv k (fun _ : ℂ => M) ρ) by ring,norm_neg,
      Real.sqrt_eq_rpow]
    exact (norm_add_le _ _).trans ((add_le_add ht hmass).trans
      ((le_of_eq (add_mul F B _).symm).trans (mul_le_mul_of_nonneg_right (le_max_right L (F+B))
        (Real.rpow_nonneg hx0.le _))))

#print axioms exists_alternating_prime_kernel_at_zero

end GaloisForLFunctions.ExceptionalLayerTheory
