import GaloisForLFunctions.RHTower.ChiRamanujanGlobalSourceDerivatives
import GaloisForLFunctions.RHTower.ChiRamanujanCubicBoundaryCancellation
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Uniform Schwartz control of the actual BAG tested sources

Every joint derivative of the literal cubic source and its contraction subtraction
has rapid frequency decay, uniform through the critical damping. A single explicit
finite family of standard Schwartz seminorms controls every derivative up to a
specified order. Actual source growth is proved upstream, never assumed here.
-/

noncomputable section
open Set Filter Metric
open scoped BigOperators Topology ContDiff SchwartzMap
namespace RHTower.BAGTrace

/-- A fixed finite family of the standard Schwartz seminorms. -/
def cubicSchwartzSeminorm (k n : ℕ) : Seminorm ℂ (𝓢(ℝ × ℝ, ℂ)) :=
  (Finset.Iic (k,n)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)

private theorem norm_iteratedFDeriv_mul_le_at
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℂ} {x : E} (n : ℕ)
    (hf : ContDiffAt ℝ (n : ℕ∞ω) f x) (hg : ContDiffAt ℝ (n : ℕ∞ω) g x) :
    ‖iteratedFDeriv ℝ n (fun y => f y*g y) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨U,hUo,hxU,hU⟩ :=
    (show ContDiffWithinAt ℝ (n : ℕ∞ω) f univ x from hf).contDiffOn' le_rfl (by simp)
  obtain ⟨V,hVo,hxV,hV⟩ :=
    (show ContDiffWithinAt ℝ (n : ℕ∞ω) g univ x from hg).contDiffOn' le_rfl (by simp)
  have hUf : ContDiffOn ℝ (n : ℕ∞ω) f U := by simpa using hU
  have hVg : ContDiffOn ℝ (n : ℕ∞ω) g V := by simpa using hV
  have hS : UniqueDiffOn ℝ (U ∩ V) := (hUo.inter hVo).uniqueDiffOn
  have hx : x ∈ U ∩ V := ⟨hxU,hxV⟩
  have h := norm_iteratedFDerivWithin_mul_le (hUf.mono inter_subset_left)
    (hVg.mono inter_subset_right) hS hx (n := n) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS (hf.mul hg) hx] at h
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hS (hf.of_le (by exact_mod_cast hin)) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hS (hg.of_le (by exact_mod_cast Nat.sub_le n i)) hx]

private theorem norm_iteratedFDeriv_comp_linear_le
    {D E : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : D →L[ℝ] E) (hg : ‖g‖ ≤ 1) {f : E → ℂ} {x : D} (n : ℕ)
    (hf : ContDiffAt ℝ (n : ℕ∞ω) f (g x)) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ n f (g x)‖ := by
  obtain ⟨U,hUo,hxU,hU⟩ :=
    (show ContDiffWithinAt ℝ (n : ℕ∞ω) f univ (g x) from hf).contDiffOn' le_rfl (by simp)
  have hUr : ContDiffOn ℝ (n : ℕ∞ω) f U := by simpa using hU
  have hpre : IsOpen (g ⁻¹' U) := hUo.preimage g.continuous
  have hcomp : ContDiffAt ℝ (n : ℕ∞ω) (f ∘ g) x := hf.comp x g.contDiff.contDiffAt
  have he := g.iteratedFDerivWithin_comp_right hUr hUo.uniqueDiffOn hpre.uniqueDiffOn hxU
    (i := n) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hcomp hxU,
    iteratedFDerivWithin_eq_iteratedFDeriv hUo.uniqueDiffOn hf hxU] at he
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n f (g x)‖*(∏ _i : Fin n, ‖g‖) :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n f (g x)‖*(∏ _i : Fin n, (1 : ℝ)) :=
      mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hg))
        (norm_nonneg _)
    _ = _ := by simp

private def cubicFrequencyProjection : (Fin 3 → ℝ) →L[ℝ] ℝ × ℝ where
  toFun w := (w 1,w 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

private theorem norm_cubicFrequencyProjection_le : ‖cubicFrequencyProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simp only [one_mul]
  exact max_le (norm_le_pi_norm w 1) (norm_le_pi_norm w 2)

private def cubicAxisProjection : (Fin 3 → ℝ) →L[ℝ] (Fin 2 → ℝ) where
  toFun w := ![w 0,w 1]
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl
  cont := by apply continuous_pi; intro i; fin_cases i <;> exact continuous_apply _

private theorem norm_cubicAxisProjection_le : ‖cubicAxisProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simp only [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg w)).mpr
  intro i
  fin_cases i <;> exact norm_le_pi_norm w _

private theorem norm_testProjection_derivative_le (Φ : 𝓢(ℝ × ℝ, ℂ)) (n : ℕ) (w : Fin 3 → ℝ) :
    ‖iteratedFDeriv ℝ n (fun x : Fin 3 → ℝ => Φ (x 1,x 2)) w‖ ≤
      ‖iteratedFDeriv ℝ n Φ (w 1,w 2)‖ :=
  norm_iteratedFDeriv_comp_linear_le cubicFrequencyProjection norm_cubicFrequencyProjection_le n
    (Φ.smooth n).contDiffAt

private theorem norm_axisProjection_derivative_le (n : ℕ) {w : Fin 3 → ℝ} (hw : 1 ≤ w 0) :
    ‖iteratedFDeriv ℝ n (fun x : Fin 3 → ℝ => realAxisSource (x 0) (x 1)) w‖ ≤
      ‖iteratedFDeriv ℝ n (fun x : Fin 2 → ℝ => realAxisSource (x 0) (x 1)) ![w 0,w 1]‖ :=
  norm_iteratedFDeriv_comp_linear_le cubicAxisProjection norm_cubicAxisProjection_le
    (f := fun x : Fin 2 → ℝ => realAxisSource (x 0) (x 1)) (x := w) n
    ((contDiffAt_realAxisSource (w := ![w 0,w 1]) hw).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))

private theorem contDiffAt_axisProjection {w : Fin 3 → ℝ} (hw : 1 ≤ w 0) :
    ContDiffAt ℝ ∞ (fun x : Fin 3 → ℝ => realAxisSource (x 0) (x 1)) w :=
  (contDiffAt_realAxisSource (w := ![w 0,w 1]) hw).comp w
    cubicAxisProjection.contDiff.contDiffAt

private theorem exists_actual_source_uniform_derivatives (n : ℕ) :
    ∃ C > 0, ∀ i ≤ n, ∀ w : Fin 3 → ℝ, w 0 ∈ Icc (1 : ℝ) 2 →
      ‖iteratedFDeriv ℝ i (fun x : Fin 3 → ℝ => realCubicSource (x 0) (x 1) (x 2)) w‖ ≤
        C*(1+|w 1|+|w 2|)^(54+9*n) ∧
      ‖iteratedFDeriv ℝ i (fun x : Fin 3 → ℝ =>
        realCubicSource (x 0) (x 1) (x 2)-realAxisSource (x 0) (x 1)) w‖ ≤
        C*(1+|w 1|+|w 2|)^(54+9*n) := by
  choose A hA hAb using exists_realCubicSource_derivative_polynomial_bound
  choose B hB hBb using exists_realAxisSource_derivative_polynomial_bound
  let C := ∑ i ∈ Finset.range (n+1), (A i+B i)
  have hCi (i : ℕ) (hi : i ≤ n) : A i+B i ≤ C :=
    Finset.single_le_sum (fun j _ => (add_pos (hA j) (hB j)).le) (Finset.mem_range_succ_iff.mpr hi)
  have hC : 0 < C := (add_pos (hA 0) (hB 0)).trans_le (hCi 0 (Nat.zero_le _))
  refine ⟨C,hC,?_⟩
  intro i hi w hw
  let T := 1+|w 1|+|w 2|
  have hT1 : 1 ≤ T := by dsimp [T]; linarith [abs_nonneg (w 1),abs_nonneg (w 2)]
  have hT : 0 < T := zero_lt_one.trans_le hT1
  have hpowA : T^(54+9*i) ≤ T^(54+9*n) := pow_le_pow_right₀ hT1 (by omega)
  have hpowB : (1+|w 1|)^(18+9*i) ≤ T^(54+9*n) :=
    (pow_le_pow_left₀ (by positivity) (by dsimp [T]; linarith [abs_nonneg (w 2)]) _).trans
      (pow_le_pow_right₀ hT1 (by omega))
  have hAa := (hAb i w hw).trans (mul_le_mul_of_nonneg_left hpowA (hA i).le)
  have hBa := (norm_axisProjection_derivative_le i hw.1).trans
    ((hBb i ![w 0,w 1] hw).trans (mul_le_mul_of_nonneg_left hpowB (hB i).le))
  have hAc : A i ≤ C := by linarith [hCi i hi,hB i]
  constructor
  · exact hAa.trans (mul_le_mul_of_nonneg_right hAc (pow_nonneg hT.le _))
  · have hf := (contDiffAt_realCubicSource (w := w) hw.1).of_le (show (i : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))
    have hg := (contDiffAt_axisProjection (w := w) hw.1).of_le (show (i : ℕ∞ω) ≤ ∞ by exact_mod_cast (le_top : (i : ℕ∞) ≤ ⊤))
    change ‖iteratedFDeriv ℝ i ((fun x : Fin 3 → ℝ => realCubicSource (x 0) (x 1) (x 2))-
      (fun x : Fin 3 → ℝ => realAxisSource (x 0) (x 1))) w‖ ≤ _
    rw [iteratedFDeriv_sub_apply hf hg]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i (fun x : Fin 3 → ℝ => realCubicSource (x 0) (x 1) (x 2)) w‖+
          ‖iteratedFDeriv ℝ i (fun x : Fin 3 → ℝ => realAxisSource (x 0) (x 1)) w‖ := norm_sub_le _ _
      _ ≤ (A i+B i)*T^(54+9*n) := by simpa only [add_mul] using add_le_add hAa hBa
      _ ≤ C*T^(54+9*n) := mul_le_mul_of_nonneg_right (hCi i hi) (pow_nonneg hT.le _)

private theorem frequency_weight_test_derivative_le (k n j : ℕ) (hj : j ≤ n)
    (Φ : 𝓢(ℝ × ℝ, ℂ)) (u v : ℝ) :
    (1+|u|+|v|)^k*‖iteratedFDeriv ℝ j Φ (u,v)‖ ≤
      2^k*(2^k*cubicSchwartzSeminorm k n Φ) := by
  have hT : 1+|u|+|v| ≤ 2*(1+‖(u,v)‖) := by
    have hu := norm_fst_le (u,v)
    have hv := norm_snd_le (u,v)
    simp only [Real.norm_eq_abs] at hu hv
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1+|u|+|v|) hT k
  have hs := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (k,n)) le_rfl hj Φ (u,v)
  calc
    _ ≤ (2*(1+‖(u,v)‖))^k*‖iteratedFDeriv ℝ j Φ (u,v)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ = 2^k*((1+‖(u,v)‖)^k*‖iteratedFDeriv ℝ j Φ (u,v)‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)

/-- Uniform control in a fixed finite Schwartz seminorm family for EVERY joint derivative
of the actual tested cubic source and its literal contraction subtraction. -/
theorem exists_cubicTestedSource_schwartz_bound (k n : ℕ) :
    ∃ C > 0, ∀ Φ : 𝓢(ℝ × ℝ, ℂ), ∀ w : Fin 3 → ℝ, w 0 ∈ Icc (1 : ℝ) 2 →
      (1+|w 1|+|w 2|)^k*‖iteratedFDeriv ℝ n (cubicTestedSource Φ) w‖ ≤
        C*cubicSchwartzSeminorm (k+54+9*n) n Φ ∧
      (1+|w 1|+|w 2|)^k*‖iteratedFDeriv ℝ n (cubicTestedAxisNumerator Φ) w‖ ≤
        C*cubicSchwartzSeminorm (k+54+9*n) n Φ := by
  obtain ⟨D,hD,hsource⟩ := exists_actual_source_uniform_derivatives n
  let L := 54+9*n
  let K := k+L
  let C := (2 : ℝ)^n*D*2^K*2^K
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro Φ w hw
  let T := 1+|w 1|+|w 2|
  have hT : 0 < T := by dsimp [T]; positivity
  have hgen {f : (Fin 3 → ℝ) → ℂ} (hf : ContDiffAt ℝ (n : ℕ∞ω) f w)
      (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f w‖ ≤ D*T^L) :
      T^k*‖iteratedFDeriv ℝ n (fun x => f x*Φ (x 1,x 2)) w‖ ≤
        C*cubicSchwartzSeminorm K n Φ := by
    have hΦ : ContDiffAt ℝ (n : ℕ∞ω) (fun x : Fin 3 → ℝ => Φ (x 1,x 2)) w :=
      (Φ.smooth n).contDiffAt.comp w cubicFrequencyProjection.contDiff.contDiffAt
    have hprod := norm_iteratedFDeriv_mul_le_at n hf hΦ
    have hsum : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ))=(2 : ℝ)^n := by
      exact_mod_cast Nat.sum_range_choose n
    calc
      _ ≤ T^k*(∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*‖iteratedFDeriv ℝ i f w‖*
          ‖iteratedFDeriv ℝ (n-i) (fun x : Fin 3 → ℝ => Φ (x 1,x 2)) w‖) :=
        mul_le_mul_of_nonneg_left hprod (pow_nonneg hT.le _)
      _ = ∑ i ∈ Finset.range (n+1), T^k*((n.choose i : ℝ)*‖iteratedFDeriv ℝ i f w‖*
          ‖iteratedFDeriv ℝ (n-i) (fun x : Fin 3 → ℝ => Φ (x 1,x 2)) w‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*D*
          (2^K*(2^K*cubicSchwartzSeminorm K n Φ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
        have hc : 0 ≤ (n.choose i : ℝ) := by positivity
        calc
          _ ≤ T^k*((n.choose i : ℝ)*(D*T^L)*‖iteratedFDeriv ℝ (n-i) Φ (w 1,w 2)‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (mul_le_mul_of_nonneg_left (hb i hin) hc)
                (norm_testProjection_derivative_le Φ (n-i) w) (norm_nonneg _) (by positivity))
              (pow_nonneg hT.le _)
          _ = (n.choose i : ℝ)*D*(T^K*‖iteratedFDeriv ℝ (n-i) Φ (w 1,w 2)‖) := by
            rw [show T^K=T^k*T^L from pow_add T k L]
            have halg (a b c d e : ℝ) : a*(b*(c*d)*e)=b*c*(a*d*e) := by ring
            exact halg _ _ _ _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (frequency_weight_test_derivative_le K n (n-i) (Nat.sub_le n i) Φ (w 1) (w 2))
            (mul_nonneg hc hD.le)
      _ = C*cubicSchwartzSeminorm K n Φ := by
        rw [← Finset.sum_mul,← Finset.sum_mul,hsum]
        dsimp only [C]
        ring
  have hKA : k+54+9*n=K := by dsimp [K,L]; omega
  rw [hKA]
  constructor
  · exact hgen ((contDiffAt_realCubicSource hw.1).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
      (fun i hi => (hsource i hi w hw).1)
  · exact hgen (((contDiffAt_realCubicSource hw.1).sub (contDiffAt_axisProjection hw.1)).of_le (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
      (fun i hi => (hsource i hi w hw).2)

theorem cubicSchwartzSeminorm_mono {k n K N : ℕ} (hk : k ≤ K) (hn : n ≤ N) :
    cubicSchwartzSeminorm k n ≤ cubicSchwartzSeminorm K N :=
  Finset.sup_mono (Finset.Iic_subset_Iic.mpr ⟨hk,hn⟩)

/-- One fixed finite Schwartz seminorm controls every derivative up to the requested order,
uniformly through the critical damping and across the entire frequency plane. -/
theorem exists_cubicTestedSource_uniform_schwartz_bound (k N : ℕ) :
    ∃ C > 0, ∀ Φ : 𝓢(ℝ × ℝ, ℂ), ∀ n ≤ N, ∀ w : Fin 3 → ℝ, w 0 ∈ Icc (1 : ℝ) 2 →
      (1+|w 1|+|w 2|)^k*‖iteratedFDeriv ℝ n (cubicTestedSource Φ) w‖ ≤
        C*cubicSchwartzSeminorm (k+54+9*N) N Φ ∧
      (1+|w 1|+|w 2|)^k*‖iteratedFDeriv ℝ n (cubicTestedAxisNumerator Φ) w‖ ≤
        C*cubicSchwartzSeminorm (k+54+9*N) N Φ := by
  choose A hA hb using exists_cubicTestedSource_schwartz_bound k
  let C := ∑ n ∈ Finset.range (N+1), A n
  have hCi (n : ℕ) (hn : n ≤ N) : A n ≤ C :=
    Finset.single_le_sum (fun j _ => (hA j).le) (Finset.mem_range_succ_iff.mpr hn)
  have hC : 0 < C := (hA 0).trans_le (hCi 0 (Nat.zero_le _))
  refine ⟨C,hC,?_⟩
  intro Φ n hn w hw
  have hs : cubicSchwartzSeminorm (k+54+9*n) n Φ ≤ cubicSchwartzSeminorm (k+54+9*N) N Φ :=
    Seminorm.le_def.mp (cubicSchwartzSeminorm_mono (by omega) hn) Φ
  have he := mul_le_mul (hCi n hn) hs (apply_nonneg _ _) hC.le
  exact ⟨(hb n Φ w hw).1.trans he,(hb n Φ w hw).2.trans he⟩

/-- In particular the actual moving cubic source times any Schwartz test is globally bounded. -/
theorem exists_bound_schwartz_realCubicSource (Φ : 𝓢(ℝ × ℝ, ℂ)) :
    ∃ B ≥ 0, ∀ σ ∈ Icc (1 : ℝ) 2, ∀ w : ℝ × ℝ,
      ‖realCubicSource σ w.1 w.2*Φ w‖ ≤ B := by
  obtain ⟨C,hC,hb⟩ := exists_cubicTestedSource_schwartz_bound 0 0
  refine ⟨C*cubicSchwartzSeminorm 54 0 Φ,mul_nonneg hC.le (apply_nonneg _ _),?_⟩
  intro σ hσ w
  simpa [cubicTestedSource] using (hb Φ ![σ,w.1,w.2] hσ).1

end RHTower.BAGTrace
