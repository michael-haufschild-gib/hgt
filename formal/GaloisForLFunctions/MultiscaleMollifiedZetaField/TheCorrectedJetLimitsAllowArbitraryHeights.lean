import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheShiftedSelbergFormKeepsItsFirstTwoDerivatives
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheCorrectedJetsAreUniformlyLipschitz

/-!
# Corrected-jet limits under arbitrary height parametrizations

Uniform Lipschitz control compares the moving shift with its fixed limit.
The cutoff may then tend to infinity along any filter. In particular, the
arithmetic limit applies when the cutoff is a floor of a real height power
and the normalized displacement depends on that real height.
-/

open Filter Polynomial Set Topology

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem correctedProfileJetSum_reindex_limit (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ I : ℝ} (hv : Tendsto v l (𝓝 v₀)) (k j : ℕ)
    (hfixed : Tendsto (fun N => correctedProfileJetSum P.eval Q.eval N (-2 * v₀) v₀ k j)
      atTop (𝓝 I)) :
    Tendsto (fun x => correctedProfileJetSum P.eval Q.eval (n x) (-2 * v x) (v x) k j)
      l (𝓝 I) := by
  let V : ℝ := |v₀| + 1
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hv₀ : v₀ ∈ Icc (-V) V := by
    constructor <;> dsimp only [V] <;> linarith only [neg_abs_le v₀, le_abs_self v₀]
  obtain ⟨K, hK, hLip⟩ := exists_uniform_correctedProfileJetSum_lipschitz P Q hP hQ hV k j
  have hvbound : ∀ᶠ x in l, v x ∈ Icc (-V) V := by
    have hh := hv.eventually (Metric.ball_mem_nhds v₀ zero_lt_one)
    filter_upwards [hh] with x hx
    rw [Real.dist_eq] at hx
    obtain ⟨hl, hu⟩ := abs_lt.mp hx
    constructor <;> dsimp only [V] <;> linarith only [hl, hu, neg_abs_le v₀, le_abs_self v₀]
  have herr : Tendsto (fun x => K * |v x - v₀|) l (𝓝 0) := by
    simpa only [sub_self, abs_zero, mul_zero] using ((hv.sub_const v₀).abs).const_mul K
  have hdifference : Tendsto (fun x =>
      correctedProfileJetSum P.eval Q.eval (n x) (-2 * v x) (v x) k j -
        correctedProfileJetSum P.eval Q.eval (n x) (-2 * v₀) v₀ k j) l (𝓝 0) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    filter_upwards [hvbound, hn.eventually hLip, herr.eventually_lt_const hε] with x hvx hNx hsmall
    rw [Real.dist_eq, sub_zero]
    exact (hNx (v x) hvx v₀ hv₀).trans_lt hsmall
  simpa only [Function.comp_def, sub_add_cancel, zero_add] using hdifference.add (hfixed.comp hn)

/-- The corrected-jet limit is joint in the cutoff and normalized shift. -/
theorem tendsto_correctedProfileJetSum_reindexed (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (k j : ℕ) :
    Tendsto (fun x => correctedProfileJetSum P.eval Q.eval (n x) (-2 * v x) (v x) k j) l
      (𝓝 (if j = 0 then polynomialProfilePairIntegral P Q v₀ k else 0)) := by
  apply correctedProfileJetSum_reindex_limit P Q hP hQ hn hv k j
  cases j with
  | zero =>
      simpa only [if_true, correctedProfileJetSum_zero_coupled, polynomialProfilePairIntegral] using
        tendsto_correctedCoupledProfileSum P Q hP hQ
          (v := fun _ : ℕ => v₀) tendsto_const_nhds k
  | succ j =>
      simpa only [Nat.succ_ne_zero, if_false] using
        tendsto_correctedProfileJetSum_succ_coupled P Q hP hQ
          (v := fun _ : ℕ => v₀) tendsto_const_nhds k j


private theorem tendsto_zeroCorrectionJet_reindexed (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (k : ℕ) :
    Tendsto (fun x => correctedProfileJetSum P.eval Q.eval (n x) (-2 * v x) (v x) k 0)
      l (𝓝 (polynomialProfilePairIntegral P Q v₀ k)) := by
  simpa only [if_true] using tendsto_correctedProfileJetSum_reindexed P Q hP hQ hn hv k 0

private theorem tendsto_positiveCorrectionJet_reindexed (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (k j : ℕ) :
    Tendsto (fun x => correctedProfileJetSum P.eval Q.eval (n x) (-2 * v x) (v x) k (j + 1))
      l (𝓝 0) := by
  simpa only [Nat.add_one_ne_zero, if_false] using
    tendsto_correctedProfileJetSum_reindexed P Q hP hQ hn hv k (j + 1)

/-- The first derivative converges for every convergent normalized shift. -/
theorem tendsto_correctedProfileFirstJet_reindexed (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (κ ν : ℝ) (k : ℕ) :
    Tendsto (fun N => correctedProfileFirstJet P.eval Q.eval (n N) (-2 * v N) (v N) κ ν k 0)
      l (𝓝 (polynomialProfileFirstLimit P Q v₀ κ ν k)) := by
  have h0 := (tendsto_positiveCorrectionJet_reindexed P Q hP hQ hn hv k 0).const_mul κ
  have h1 := (tendsto_zeroCorrectionJet_reindexed P Q hP hQ hn hv (k + 1)).const_mul κ
  have h2 := (tendsto_zeroCorrectionJet_reindexed (complementPolynomial P) Q
    (complementPolynomial_eval_zero P hP) hQ hn hv k).const_mul ν
  have h3 := (tendsto_zeroCorrectionJet_reindexed P (complementPolynomial Q)
    hP (complementPolynomial_eval_zero Q hQ) hn hv k).const_mul ν
  simpa only [correctedProfileFirstJet, polynomialProfileFirstLimit,
    complementPolynomial_eval, mul_zero, zero_add] using ((h0.add h1).add h2).add h3

/-- A further directional derivative does not restore a vanished correction jet. -/
theorem tendsto_correctedProfileFirstJet_succ_reindexed (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (κ ν : ℝ) (k j : ℕ) :
    Tendsto (fun N => correctedProfileFirstJet P.eval Q.eval (n N) (-2 * v N) (v N) κ ν k (j + 1))
      l (𝓝 0) := by
  have h0 := (tendsto_positiveCorrectionJet_reindexed P Q hP hQ hn hv k (j + 1)).const_mul κ
  have h1 := (tendsto_positiveCorrectionJet_reindexed P Q hP hQ hn hv (k + 1) j).const_mul κ
  have h2 := (tendsto_positiveCorrectionJet_reindexed (complementPolynomial P) Q
    (complementPolynomial_eval_zero P hP) hQ hn hv k j).const_mul ν
  have h3 := (tendsto_positiveCorrectionJet_reindexed P (complementPolynomial Q)
    hP (complementPolynomial_eval_zero Q hQ) hn hv k j).const_mul ν
  simpa only [correctedProfileFirstJet, complementPolynomial_eval, mul_zero, zero_add] using
    ((h0.add h1).add h2).add h3

/-- The second derivative converges to the polynomial second-jet integral. -/
theorem tendsto_correctedProfileSecondJet_reindexed (P Q : ℝ[X])
    (hP : P.eval 0 = 0) (hQ : Q.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (κ ν : ℝ) (k : ℕ) :
    Tendsto (fun N => correctedProfileSecondJet P.eval Q.eval (n N) (-2 * v N) (v N) κ ν k 0)
      l (𝓝 (polynomialProfileSecondLimit P Q v₀ κ ν k)) := by
  have h0 := (tendsto_correctedProfileFirstJet_succ_reindexed P Q hP hQ hn hv κ ν k 0).const_mul κ
  have h1 := (tendsto_correctedProfileFirstJet_reindexed P Q hP hQ hn hv κ ν (k + 1)).const_mul κ
  have h2 := (tendsto_correctedProfileFirstJet_reindexed (complementPolynomial P) Q
    (complementPolynomial_eval_zero P hP) hQ hn hv κ ν k).const_mul ν
  have h3 := (tendsto_correctedProfileFirstJet_reindexed P (complementPolynomial Q)
    hP (complementPolynomial_eval_zero Q hQ) hn hv κ ν k).const_mul ν
  simpa only [correctedProfileSecondJet, polynomialProfileSecondLimit,
    complementPolynomial_eval, mul_zero, zero_add] using ((h0.add h1).add h2).add h3


/-- The literal coupled form converges for arbitrary cutoffs tending to infinity. -/
theorem tendsto_coupledShiftedSelbergForm_reindexed (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun x => coupledShiftedSelbergForm P.eval (n x) (v x)) l
      (𝓝 (∫ t : ℝ in 0..1, (P.derivative.eval (1 - t) - v₀ * P.eval (1 - t)) ^ 2)) := by
  simpa only [coupledShiftedSelbergForm, shiftedSelbergProfileForm_eq_correctedProfileJetSum,
    polynomialProfilePairIntegral, pow_zero, one_mul, pow_two] using
    tendsto_zeroCorrectionJet_reindexed P P hP hP hn hv 0

/-- The first frozen-direction derivative has its polynomial integral limit. -/
theorem tendsto_shiftedSelbergProfileForm_deriv_reindexed (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (κ ν : ℝ) :
    Tendsto (fun N => deriv (fun z =>
      shiftedSelbergProfileForm P.eval (n N) (-2 * v N + κ * z) (v N + ν * z)) 0)
      l (𝓝 (polynomialProfileFirstLimit P P v₀ κ ν 0)) := by
  have he (N : ι) := (shiftedSelbergProfileForm_derivatives P.eval (n N) (-2 * v N) (v N) κ ν).1
  simp_rw [he]
  exact tendsto_correctedProfileFirstJet_reindexed P P hP hP hn hv κ ν 0

/-- The second frozen-direction derivative has its polynomial integral limit. -/
theorem tendsto_shiftedSelbergProfileForm_iteratedDeriv_two_reindexed (P : ℝ[X]) (hP : P.eval 0 = 0)
    {ι : Type*} {l : Filter ι} {n : ι → ℕ} (hn : Tendsto n l atTop)
    {v : ι → ℝ} {v₀ : ℝ} (hv : Tendsto v l (𝓝 v₀)) (κ ν : ℝ) :
    Tendsto (fun N => iteratedDeriv 2 (fun z =>
      shiftedSelbergProfileForm P.eval (n N) (-2 * v N + κ * z) (v N + ν * z)) 0)
      l (𝓝 (polynomialProfileSecondLimit P P v₀ κ ν 0)) := by
  have he (N : ι) := (shiftedSelbergProfileForm_derivatives P.eval (n N) (-2 * v N) (v N) κ ν).2
  simp_rw [he]
  exact tendsto_correctedProfileSecondJet_reindexed P P hP hP hn hv κ ν 0

end GaloisForLFunctions.MultiscaleMollifiedZetaField
