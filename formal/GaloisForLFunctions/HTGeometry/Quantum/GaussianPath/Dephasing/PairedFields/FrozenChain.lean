import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.PhysicalDates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AccuracyScales.TenthPlateau.NonAbelianClawOnset

/-! # A single frozen physical chain and a single auxiliary Gaussian chain -/

open MeasureTheory ProbabilityTheory Filter Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
noncomputable section

local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

abbrev twoChains := pathPauliDisorderLaw.prod pathPauliDisorderLaw

/-- Inverse field rotation. Its positively displaced generator is the
original physical prefix at every size, including for size-dependent angles. -/
def observationPair (n : ℕ) (a b : ℝ) (ω : PathPauliDisorder × PathPauliDisorder) : FieldPair n :=
  fun i =>
    let h := pathPauliDisorderShell ω.1 n i
    let g := pathPauliDisorderShell ω.2 n i
    (a*h+b*g,b*h-a*g)

/-- At each prefix, inverse rotation preserves the independent product Gaussian law. -/
theorem observation_law (n : ℕ) {a b : ℝ} (hab : a^2+b^2=1) :
    MeasurePreserving (observationPair n a b) twoChains (pairLaw n) := by
  let γ := gaussianReal 0 1
  let M : Matrix (Fin 2) (Fin 2) ℝ := !![a,b;b,-a]
  have hM : Mᵀ*M=1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M,Matrix.mul_apply,Fin.sum_univ_two] <;> nlinarith only [hab]
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

/-- Undoing the rotation recovers the original prefix coefficient by coefficient. -/
theorem recover_physical (n : ℕ) {a b : ℝ} (hab : a^2+b^2=1) (ω) :
    rotated a b (observationPair n a b ω) = fun i => pathPauliDisorderShell ω.1 n i := by
  funext i
  dsimp only [rotated,observationPair]
  calc
    _ = (a^2+b^2)*pathPauliDisorderShell ω.1 n i := by ring
    _ = _ := by rw [hab,one_mul]

/-- At phase scale L through T = 2^K K^6 L² R², the same physical chain
has normalized RMS error at most 1/(KR), eventually almost surely.
Both scales may vary deterministically with the prefix. -/
theorem frozen_chain_prediction (phaseScale magnification : ℕ → ℝ) :
    ∀ᵐ ω ∂twoChains, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let D := (2:ℝ)^(n+2)
      let R := max 1 (magnification n)
      let L := max 1 (phaseScale n)
      let T := D*K^6*L^2*R^2
      let b := L/T
      let a := Real.sqrt (1-b^2)
      let x := observationPair n a b ω
      ∀ t : ℝ, |t| ≤ T → predictionError (generator (base x))
        (generator fun i => pathPauliDisorderShell ω.1 n i) t ≤ D*(1/(K*R))^2 := by
  let K (n : ℕ) : ℝ := (n+2:ℕ)
  let D (n : ℕ) := (2:ℝ)^(n+2)
  let R (n : ℕ) := max 1 (magnification n)
  let L (n : ℕ) := max 1 (phaseScale n)
  let T (n : ℕ) := D n*(K n)^6*(L n)^2*(R n)^2
  let b (n : ℕ) := L n/T n
  let a (n : ℕ) := Real.sqrt (1-(b n)^2)
  let bad (n : ℕ) : Set (FieldPair n) := {x | ∃ t : ℝ, |t| ≤ T n ∧
    D n*(1/(K n*R n))^2 < pairedError (a n) (b n) x t}
  let event (n : ℕ) := observationPair n (a n) (b n) ⁻¹' bad n
  have hk (n : ℕ) : 1 ≤ K n := by dsimp only [K]; exact_mod_cast (by omega : 1≤n+2)
  have hk₀ (n : ℕ) : 0<K n := zero_lt_one.trans_le (hk n)
  have hd (n : ℕ) : 1 ≤ D n := one_le_pow₀ (by norm_num)
  have hr (n : ℕ) : 1 ≤ R n := le_max_left ..
  have hr₀ (n : ℕ) : 0<R n := zero_lt_one.trans_le (hr n)
  have hL (n : ℕ) : 1 ≤ L n := le_max_left ..
  have hL₀ (n : ℕ) : 0<L n := zero_lt_one.trans_le (hL n)
  have ht (n : ℕ) : L n ≤ T n := by
    calc
      L n ≤ (L n)^2 := le_self_pow₀ (hL n) (by norm_num)
      _ ≤ D n*(K n)^6*(L n)^2 := le_mul_of_one_le_left (sq_nonneg _) (one_le_mul_of_one_le_of_one_le
        (hd n) (one_le_pow₀ (hk n)))
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (hr n))
  have ht₀ (n : ℕ) : 0<T n := (hL₀ n).trans_le (ht n)
  have hsq (n : ℕ) : (a n)^2+(b n)^2=1 := by
    have hb₀ : 0 ≤ b n := div_nonneg (hL₀ n).le (ht₀ n).le
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
    have hρ := one_div_pos.mpr (mul_pos (hk₀ n) (hr₀ n))
    apply (hh.trans (gaussian_uniform_prediction n (Real.sqrt_nonneg _) (hsq n) (ht₀ n) hρ)).trans
    have ha₁ : a n ≤ 1 := by nlinarith only [hsq n,sq_nonneg (b n),sq_nonneg (a n-1)]
    have hloss : 1-a n ≤ (b n)^2 := by
      nlinarith only [hsq n,mul_nonneg (Real.sqrt_nonneg (1-(b n)^2)) (sub_nonneg.mpr ha₁)]
    have hc : Real.sqrt (Fintype.card (PathLabel n)) ≤ 4*K n := by
      apply (Real.sqrt_le_iff).mpr
      refine ⟨mul_nonneg (by norm_num) (hk₀ n).le,?_⟩
      simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Nat.cast_add,
        Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,K]
      nlinarith only [sq_nonneg (n:ℝ),(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    calc
      _ ≤ 8*T n*(b n)^2*D n*(4*K n)/(1/(K n*R n))^2 := by
        change 8*T n*(1-a n)*D n*Real.sqrt _/(1/(K n*R n))^2 ≤ _
        gcongr
      _ = _ := by
        dsimp only [b,T]
        field_simp [(hL₀ n).ne',(hr₀ n).ne',(hk₀ n).ne',(zero_lt_one.trans_le (hd n)).ne']
        ring
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
  intro K' D' R' L' T' b' a' x t ht'
  have h : pairedError (a n) (b n) x t ≤ D n*(1/(K n*R n))^2 :=
    le_of_not_gt (fun he => hn ⟨t,ht',he⟩)
  have h₁ : predictionError (generator (base x)) (generator (rotated (a n) (b n) x)) t ≤ D n*(1/(K n*R n))^2 :=
    (le_add_of_nonneg_right (hsNormSq_nonneg _)).trans h
  rwa [recover_physical n (hsq n) ω] at h₁

/-- At prescribed phase scale L, every budget's best projective operator
error differs by at most 1/K from that for affine phases, at every date
through D² K^6 L². The physical and auxiliary chains are each drawn once. -/
theorem frozen_circuit_distance (phaseScale : ℕ → ℝ) :
    ∀ᵐ ω ∂twoChains, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let D := (2:ℝ)^(n+2)
      let L := max 1 (phaseScale n)
      let T := D^2*K^6*L^2
      let b := L/T
      let a := Real.sqrt (1-b^2)
      let x := observationPair n a b ω
      let B := generator (fun i => pathPauliDisorderShell ω.1 n i)
      ∀ t : ℝ, |t| ≤ T → ∀ s : ℕ,
        let V := diagonalPrediction (generator (base x)).2.isHermitian.eigenvectorUnitary B.val t
        let S := phaseCircuitMatrixImageAtMost (n+2) s
        |Metric.infDist (unitaryEvolution B.val t) S-Metric.infDist V S| ≤ 1/K := by
  have hp := frozen_chain_prediction phaseScale (fun n => Real.sqrt ((2:ℝ)^(n+2)))
  filter_upwards [hp] with ω hω
  filter_upwards [hω] with n hn
  intro K D L T b a x B t ht s V S
  have hd : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hr : 1 ≤ Real.sqrt D := Real.one_le_sqrt.mpr hd
  have hT : D*K^6*L^2*(max 1 (Real.sqrt D))^2=T := by
    rw [max_eq_right hr,Real.sq_sqrt (zero_le_one.trans hd)]
    dsimp only [T]
    ring
  let b' := L/(D*K^6*L^2*(max 1 (Real.sqrt D))^2)
  have hb : b'=b := congrArg (fun z : ℝ => L/z) hT
  have h : predictionError (generator (base (observationPair n (Real.sqrt (1-b'^2)) b' ω))) B t ≤
      D*(1/(K*max 1 (Real.sqrt D)))^2 := hn t (ht.trans hT.ge)
  rw [hb,max_eq_right hr] at h
  change hsNormSq (unitaryEvolution B.val t-V) ≤ D*(1/(K*Real.sqrt D))^2 at h
  have hk : 0<K := by dsimp only [K]; positivity
  have he : D*(1/(K*Real.sqrt D))^2=(1/K)^2 := by
    rw [div_pow,mul_pow,Real.sq_sqrt (zero_le_one.trans hd)]
    field_simp [(zero_lt_one.trans_le hd).ne',hk.ne']
  rw [he] at h
  have hhs : hsNorm (unitaryEvolution B.val t-V) ≤ 1/K := by
    apply (sq_le_sq₀ (hsNorm_nonneg _) (one_div_pos.mpr hk).le).mp
    rwa [hsNorm_sq,Finset.sum_comm]
  have hdist := (Metric.lipschitz_infDist_pt S).dist_le_mul (unitaryEvolution B.val t) V
  simp only [one_mul,NNReal.coe_one,dist_eq_norm] at hdist
  exact hdist.trans ((l2_opNorm_le_hsNorm _).trans hhs)

#print axioms frozen_circuit_distance
#print axioms frozen_chain_prediction
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
