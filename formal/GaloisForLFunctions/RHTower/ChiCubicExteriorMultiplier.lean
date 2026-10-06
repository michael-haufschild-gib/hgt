import GaloisForLFunctions.RHTower.ChiCubicNormalFourierBudgets
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-!
# The complete shrinking-cone inverse-power multiplier

A fixed actual smooth cutoff removes the zero-defect neighborhood.
Every derivative of the regularized inverse power is bounded globally.
Composition with the full signed quadratic defect and the full Leibniz
sum give finite Schwartz seminorm control, with recipient indices and
cone-width derivative cost selected before the normal iteration order.
Both signs and all frequencies are retained.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff FourierTransform
namespace RHTower.BAGTrace
private abbrev E := BAGPhysicalSpace
private theorem fin_le (n : ℕ) : (n : ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)

/-- One fixed smooth cutoff for the entire signed cone. -/
def bagCubicConeCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := by norm_num

/-- Smooth inverse-defect power, with its singular neighborhood removed. -/
def bagCubicExteriorInversePower (k : ℕ) (t : ℝ) : ℝ :=
  (1-bagCubicConeCutoff t)/t^k

theorem bagCubicExteriorInversePower_contDiff (k : ℕ) :
    ContDiff ℝ ∞ (bagCubicExteriorInversePower k) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t = 0
  · subst t
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [bagCubicConeCutoff.eventuallyEq_one] with x hx
    simp [bagCubicExteriorInversePower, hx]
  · exact (contDiffAt_const.sub bagCubicConeCutoff.contDiff.contDiffAt).div
      (contDiffAt_id.pow k) (pow_ne_zero k ht)

private theorem outside_germ (k : ℕ) (t : ℝ) (ht : 2 < |t|) :
    bagCubicExteriorInversePower k =ᶠ[𝓝 t] (fun x : ℝ => x^(-(k : ℤ))) := by
  have hn : ∀ᶠ x : ℝ in 𝓝 t, 2 < |x| :=
    (isOpen_lt continuous_const continuous_abs).mem_nhds ht
  filter_upwards [hn] with x hx
  have hz : bagCubicConeCutoff x = 0 := bagCubicConeCutoff.zero_of_le_dist
    (by simpa only [bagCubicConeCutoff, Real.dist_eq, sub_zero] using hx.le)
  simp [bagCubicExteriorInversePower, hz, zpow_neg, zpow_natCast, one_div]

/-- Every derivative is bounded on the WHOLE real line: the zero
neighborhood, both transition intervals, and both infinite ends. -/
theorem bagCubicExteriorInversePower_uniform_jets (k n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖iteratedFDeriv ℝ n (bagCubicExteriorInversePower k) t‖ ≤ C := by
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-3 : ℝ) 3)).exists_bound_of_continuousOn
    ((bagCubicExteriorInversePower_contDiff k).continuous_iteratedFDeriv (fin_le n)).continuousOn
  let A : ℝ := ‖∏ i ∈ Finset.range n, (-(k : ℝ) - i)‖
  refine ⟨max B A+1,by dsimp only [A]; positivity,fun t => ?_⟩
  by_cases ht : t ∈ Icc (-3 : ℝ) 3
  · exact (hB t ht).trans (by linarith [le_max_left B A])
  · have habs : 3 < |t| := by
      rw [mem_Icc, not_and_or] at ht
      rcases ht with ht | ht
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs t)
      · exact lt_of_lt_of_le (by linarith) (le_abs_self t)
    rw [((outside_germ k t (by linarith)).iteratedFDeriv ℝ n).eq_of_nhds,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_zpow]
    have he : -(k : ℤ) - n = -((k+n : ℕ) : ℤ) := by omega
    rw [he, zpow_neg, zpow_natCast, norm_mul, norm_inv, norm_pow]
    have hp : (‖t‖^(k+n))⁻¹ ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact one_le_pow₀ (by simpa only [Real.norm_eq_abs] using (show 1 ≤ |t| by linarith))
    have hc : ‖∏ i ∈ Finset.range n, (((-(k : ℤ) : ℤ) : ℝ) - i)‖ = A := by simp [A]
    rw [hc]
    calc
      _ ≤ A*1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ max B A+1 := by rw [mul_one]; linarith [le_max_right B A]


/-- The full signed quadratic defect, without a sheet or frequency restriction. -/
def bagCubicSignedDefect (x : E) : ℝ := x 2+x 0*x 1

private theorem defect_growth : bagCubicSignedDefect.HasTemperateGrowth :=
  (EuclideanSpace.proj (2 : Fin 3)).hasTemperateGrowth.add
    ((EuclideanSpace.proj (0 : Fin 3)).hasTemperateGrowth.mul
      (EuclideanSpace.proj (1 : Fin 3)).hasTemperateGrowth)

/-- The complete inverse-power multiplier at a shrinking cone width. -/
def bagCubicExteriorMultiplier (k : ℕ) (ε : ℝ) (x : E) : ℝ :=
  bagCubicExteriorInversePower k (ε⁻¹*bagCubicSignedDefect x)

/-- All jets through order n have a common polynomial degree fixed BEFORE
normal order k. Only the constant depends on k. Both signs and infinity
are included. -/
theorem bagCubicExteriorMultiplier_uniform_jets (n : ℕ) :
    ∃ L : ℕ, ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ ε : {r : ℝ // r ∈ Ioc (0 : ℝ) 1}, ∀ i ≤ n, ∀ x : E,
        ‖iteratedFDeriv ℝ i (bagCubicExteriorMultiplier k ε.1) x‖ ≤
          C/ε.1^n*(1+‖x‖)^L := by
  obtain ⟨l,A,hA,hAb⟩ := defect_growth.norm_iteratedFDeriv_le_uniform n
  let B : ℝ := A+1
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  refine ⟨l*n,fun k => ?_⟩
  choose C hC hCb using bagCubicExteriorInversePower_uniform_jets k
  let C₀ : ℝ := 1+∑ j ∈ Finset.range (n+1), C j
  have hC₀ : 0 < C₀ := by
    have hs : 0 ≤ ∑ j ∈ Finset.range (n+1), C j := Finset.sum_nonneg (fun j _ => (hC j).le)
    dsimp only [C₀]; linarith
  have hCC₀ (j : ℕ) (hj : j ≤ n) : C j ≤ C₀ :=
    (Finset.single_le_sum (fun j _ => (hC j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans (by dsimp only [C₀]; linarith)
  refine ⟨(n.factorial : ℝ)*C₀*B^n,by positivity,fun ε i hi x => ?_⟩
  have hεinv : 1 ≤ ε.1⁻¹ := (one_le_inv₀ ε.2.1).mpr ε.2.2
  let R : ℝ := ε.1⁻¹*B*(1+‖x‖)^l
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hεinv hB)
    (one_le_pow₀ (by linarith [norm_nonneg x]))
  have hd (j : ℕ) (hj : 1 ≤ j) (hji : j ≤ i) :
      ‖iteratedFDerivWithin ℝ j (fun y => ε.1⁻¹*bagCubicSignedDefect y) univ x‖ ≤ R^j := by
    rw [iteratedFDerivWithin_univ]
    change ‖iteratedFDeriv ℝ j (fun y => ε.1⁻¹ • bagCubicSignedDefect y) x‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' (defect_growth.1.contDiffAt.of_le (fin_le j)),
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ε.2.1)]
    calc
      _ ≤ ε.1⁻¹*(A*(1+‖x‖)^l) := mul_le_mul_of_nonneg_left (hAb j (hji.trans hi) x)
        (inv_nonneg.mpr ε.2.1.le)
      _ ≤ R := by
        dsimp only [R]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by dsimp only [B]; linarith)
            (pow_nonneg (by positivity) l)) (inv_nonneg.mpr ε.2.1.le)
      _ ≤ R^j := le_self_pow₀ hR (by omega)
  have ho (j : ℕ) (hj : j ≤ i) :
      ‖iteratedFDerivWithin ℝ j (bagCubicExteriorInversePower k) univ
        (ε.1⁻¹*bagCubicSignedDefect x)‖ ≤ C₀ := by
    rw [iteratedFDerivWithin_univ]
    exact (hCb j _).trans (hCC₀ j (hj.trans hi))
  have hb := norm_iteratedFDerivWithin_comp_le
    (bagCubicExteriorInversePower_contDiff k).contDiffOn
    ((contDiff_const.mul defect_growth.1).contDiffOn) (fin_le i)
    uniqueDiffOn_univ uniqueDiffOn_univ (mapsTo_univ _ _) (mem_univ x) ho hd
  rw [iteratedFDerivWithin_univ] at hb
  change ‖iteratedFDeriv ℝ i (bagCubicExteriorMultiplier k ε.1) x‖ ≤ _ at hb
  calc
    _ ≤ (i.factorial : ℝ)*C₀*R^i := hb
    _ ≤ (n.factorial : ℝ)*C₀*R^n := mul_le_mul
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hi) hC₀.le)
      (pow_le_pow_right₀ hR hi) (pow_nonneg (by linarith) i) (by positivity)
    _ = _ := by dsimp only [R]; rw [mul_pow,mul_pow,inv_pow,←pow_mul]; ring

theorem bagCubicExteriorMultiplier_hasTemperateGrowth (k : ℕ) (ε : ℝ) :
    (bagCubicExteriorMultiplier k ε).HasTemperateGrowth := by
  have hg : (bagCubicExteriorInversePower k).HasTemperateGrowth := by
    refine ⟨bagCubicExteriorInversePower_contDiff k,fun n => ?_⟩
    obtain ⟨C,_,hC⟩ := bagCubicExteriorInversePower_uniform_jets k n
    exact ⟨0,C,fun x => by simpa only [pow_zero,mul_one] using hC x⟩
  exact hg.comp ((Function.HasTemperateGrowth.const ε⁻¹).mul defect_growth)


/-- Multiplication by the complete smooth inverse-defect power. -/
def bagCubicExteriorMultiply (k : ℕ) (ε : ℝ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.smulLeftCLM ℂ (bagCubicExteriorMultiplier k ε) f

@[simp] theorem bagCubicExteriorMultiply_apply (k : ℕ) (ε : ℝ)
    (f : SchwartzMap E ℂ) (x : E) :
    bagCubicExteriorMultiply k ε f x = bagCubicExteriorMultiplier k ε x • f x :=
  SchwartzMap.smulLeftCLM_apply_apply (bagCubicExteriorMultiplier_hasTemperateGrowth k ε) f x

/-- Every recipient seminorm costs a fixed finite family of input
seminorms, selected BEFORE normal order k. The full multiplier is used. -/
theorem bagCubicExteriorMultiply_seminorm (p n : ℕ) :
    ∃ K : Finset (ℕ × ℕ), ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ ε : {r : ℝ // r ∈ Ioc (0 : ℝ) 1}, ∀ f : SchwartzMap E ℂ,
        SchwartzMap.seminorm ℂ p n (bagCubicExteriorMultiply k ε.1 f) ≤
          C/ε.1^n*(K.sup (schwartzSeminormFamily ℂ E ℂ)) f := by
  obtain ⟨L,hL⟩ := bagCubicExteriorMultiplier_uniform_jets n
  refine ⟨Finset.Iic (p+L,n),fun k => ?_⟩
  obtain ⟨C,hC,hCb⟩ := hL k
  let S : ℝ := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _)
  refine ⟨C*2^(p+L)*S+1,by positivity,fun ε f => ?_⟩
  have hε : 0 < ε.1 := ε.2.1
  let Q := (Finset.Iic (p+L,n)).sup (schwartzSeminormFamily ℂ E ℂ)
  have hQ : 0 ≤ Q f := apply_nonneg _ _
  apply SchwartzMap.seminorm_le_bound ℂ p n _ (by positivity)
  intro x
  have he : (bagCubicExteriorMultiply k ε.1 f : E → ℂ) =
      fun y => bagCubicExteriorMultiplier k ε.1 y • f y := by
    funext y; exact bagCubicExteriorMultiply_apply k ε.1 f y
  rw [he]
  have hb := norm_iteratedFDeriv_smul_le
    (bagCubicExteriorMultiplier_hasTemperateGrowth k ε.1).1 (f.smooth ⊤) x (fin_le n)
  calc
    _ ≤ ‖x‖^p * (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*
        ‖iteratedFDeriv ℝ i (bagCubicExteriorMultiplier k ε.1) x‖ *
        ‖iteratedFDeriv ℝ (n-i) f x‖) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*(C/ε.1^n)*2^(p+L)*Q f := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hw := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
        (m := (p+L,n)) le_rfl (Nat.sub_le n i) f x
      calc
        _ ≤ (1+‖x‖)^p*((n.choose i : ℝ)*(C/ε.1^n*(1+‖x‖)^L)*
            ‖iteratedFDeriv ℝ (n-i) f x‖) := by
          gcongr
          · linarith [norm_nonneg x]
          · exact hCb ε i hin x
        _ = (n.choose i : ℝ)*(C/ε.1^n)*((1+‖x‖)^(p+L)*
            ‖iteratedFDeriv ℝ (n-i) f x‖) := by rw [pow_add]; ring
        _ ≤ (n.choose i : ℝ)*(C/ε.1^n)*(2^(p+L)*Q f) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
        _ = _ := by ring
    _ = C*2^(p+L)*S/ε.1^n*Q f := by dsimp only [S]; rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.sum_mul]; ring
    _ ≤ _ := by gcongr; linarith

end RHTower.BAGTrace
