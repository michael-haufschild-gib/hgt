import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.PhysicalDates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NonAbelianClawOnset

/-! # A single frozen physical chain and a single auxiliary Gaussian chain -/

open MeasureTheory ProbabilityTheory Filter Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
noncomputable section

abbrev twoChains := pathPauliDisorderLaw.prod pathPauliDisorderLaw

/-- Inverse field rotation. Its positively displaced generator is the
original physical prefix at every size, including for size-dependent angles. -/
def observationPair (n : ℕ) (a b : ℝ) (ω : PathPauliDisorder × PathPauliDisorder) : FieldPair n :=
  fun i =>
    let h := pathPauliDisorderShell ω.1 n i
    let g := pathPauliDisorderShell ω.2 n i
    (a*h+b*g,b*h-a*g)

private theorem observation_law (n : ℕ) {a b : ℝ} (hab : a^2+b^2=1) :
    MeasurePreserving (observationPair n a b) twoChains (pairLaw n) := by
  let γ := gaussianReal 0 1
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;b,-a]
  have hM : Mᵀ*M=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply] <;> nlinarith only [hab]
  have hR := AccuracyScales.TenthPlateau.measurePreserving_pi_gaussian_orthogonal M hM
    (mul_eq_one_comm.mp hM)
  have h₂ := measurePreserving_finTwoArrow γ
  let rotate (z : ℝ × ℝ) := (a*z.1+b*z.2,b*z.1-a*z.2)
  have hs : MeasurePreserving rotate (γ.prod γ) (γ.prod γ) := by
    convert h₂.comp (hR.comp h₂.symm) using 1
    funext z
    apply Prod.ext
    · change _=(M *ᵥ ![z.1,z.2]) 0
      simp [rotate,M,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    · change _=(M *ᵥ ![z.1,z.2]) 1
      simp [rotate,M,Matrix.mulVec,dotProduct,Fin.sum_univ_two,sub_eq_add_neg]
  have hr := measurePreserving_pi (fun _ : PathLabel n => γ.prod γ) (fun _ => γ.prod γ)
    (f:=fun _ => rotate) (fun _ => hs)
  have hsplit := measurePreserving_arrowProdEquivProdArrow ℝ ℝ (PathLabel n)
    (fun _ => γ) (fun _ => γ)
  exact hr.comp (hsplit.symm.comp ((BlockDilations.prefix_measure n).prod (BlockDilations.prefix_measure n)))

private theorem recover_physical (n : ℕ) {a b : ℝ} (hab : a^2+b^2=1) (ω) :
    rotated a b (observationPair n a b ω) = fun i => pathPauliDisorderShell ω.1 n i := by
  funext i
  dsimp only [rotated,observationPair]
  calc
    _ = (a^2+b^2)*pathPauliDisorderShell ω.1 n i := by ring
    _ = _ := by rw [hab,one_mul]

/-- Through T = 2^K K^8 the true frozen prefix has normalized RMS
prediction error at most 1/K, eventually almost surely. The independent
field has phase scale K at the horizon. The original disorder is fixed
across prefixes and dates. -/
theorem frozen_chain_prediction :
    ∀ᵐ ω ∂twoChains, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let D := (2:ℝ)^(n+2)
      let T := D*K^8
      let b := K/T
      let a := Real.sqrt (1-b^2)
      let x := observationPair n a b ω
      ∀ t : ℝ, |t| ≤ T → predictionError (generator (base x))
        (generator fun i => pathPauliDisorderShell ω.1 n i) t ≤ D*(1/K)^2 := by
  let K (n : ℕ) : ℝ := (n+2:ℕ)
  let D (n : ℕ) := (2:ℝ)^(n+2)
  let T (n : ℕ) := D n*(K n)^8
  let b (n : ℕ) := K n/T n
  let a (n : ℕ) := Real.sqrt (1-(b n)^2)
  let bad (n : ℕ) : Set (FieldPair n) := {x | ∃ t : ℝ, |t| ≤ T n ∧
    D n*(1/K n)^2 < pairedError (a n) (b n) x t}
  let event (n : ℕ) := observationPair n (a n) (b n) ⁻¹' bad n
  have hk (n : ℕ) : 1 ≤ K n := by dsimp only [K]; exact_mod_cast (by omega : 1≤n+2)
  have hk₀ (n : ℕ) : 0<K n := zero_lt_one.trans_le (hk n)
  have hd (n : ℕ) : 1 ≤ D n := one_le_pow₀ (by norm_num)
  have ht (n : ℕ) : K n ≤ T n := by
    apply le_trans _ (le_mul_of_one_le_left (by positivity) (hd n))
    exact (le_self_pow₀ (hk n) (by norm_num : 8≠0))
  have ht₀ (n : ℕ) : 0<T n := (hk₀ n).trans_le (ht n)
  have hsq (n : ℕ) : (a n)^2+(b n)^2=1 := by
    have hb₀ : 0 ≤ b n := div_nonneg (hk₀ n).le (ht₀ n).le
    have hb : b n ≤ 1 := (div_le_one (ht₀ n)).mpr (ht n)
    have h := mul_le_mul_of_nonneg_left hb hb₀
    rw [mul_one,←sq] at h
    rw [show (a n)^2=1-(b n)^2 from Real.sq_sqrt (sub_nonneg.mpr (h.trans hb))]
    ring
  have hcost (n : ℕ) : twoChains.real (event n) ≤ 32/(K n)^3 := by
    have hmap := observation_law n (hsq n)
    have hle := Measure.le_map_apply (μ:=twoChains) hmap.measurable.aemeasurable (bad n)
    rw [hmap.map_eq] at hle
    have hh : twoChains.real (event n) ≤ (pairLaw n).real (bad n) :=
      ENNReal.toReal_mono (measure_ne_top _ _) hle
    have hρ := one_div_pos.mpr (hk₀ n)
    apply (hh.trans (gaussian_uniform_prediction n (Real.sqrt_nonneg _) (hsq n) (ht₀ n) hρ)).trans
    have ha₁ : a n ≤ 1 := by nlinarith only [hsq n,sq_nonneg (b n),sq_nonneg (a n-1)]
    have hloss : 1-a n ≤ (b n)^2 := by
      nlinarith only [hsq n,mul_nonneg (Real.sqrt_nonneg (1-(b n)^2)) (sub_nonneg.mpr ha₁)]
    have hc : Real.sqrt (Fintype.card (PathLabel n)) ≤ 4*K n := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨mul_nonneg (by norm_num) (hk₀ n).le,?_⟩
      simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.cast_add,
        Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,K]
      nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg n]
    calc
      _ ≤ 8*T n*(b n)^2*D n*(4*K n)/(1/K n)^2 := by
        change 8*T n*(1-a n)*D n*Real.sqrt _/(1/K n)^2 ≤ _
        gcongr <;> assumption
      _ = _ := by
        dsimp only [b,T]
        field_simp [(hk₀ n).ne',(zero_lt_one.trans_le (hd n)).ne']
        <;> ring
  have hp : Summable (fun n : ℕ => (1:ℝ)/(n:ℝ)^3) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hsum : Summable (fun n => twoChains.real (event n)) := by
    have hshift := ((summable_nat_add_iff 2).mpr hp).mul_left 32
    apply hshift.of_norm_bounded
    intro n
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact (hcost n).trans_eq (by dsimp only [K]; ring)
  have hf : ∀ᵐ ω ∂twoChains, ∀ᶠ n : ℕ in atTop, ω∉event n := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top twoChains _)] using hsum.tsum_ofReal_ne_top
  filter_upwards [hf] with ω hω
  filter_upwards [hω] with n hn
  intro K' D' T' b' a' x t ht'
  have h : pairedError (a n) (b n) x t ≤ D n*(1/K n)^2 :=
    le_of_not_gt (fun he => hn ⟨t,ht',he⟩)
  have h₁ : predictionError (generator (base x)) (generator (rotated (a n) (b n) x)) t ≤ D n*(1/K n)^2 :=
    (le_add_of_nonneg_right (hsNormSq_nonneg _)).trans h
  rwa [recover_physical n (hsq n) ω] at h₁

#print axioms frozen_chain_prediction
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
