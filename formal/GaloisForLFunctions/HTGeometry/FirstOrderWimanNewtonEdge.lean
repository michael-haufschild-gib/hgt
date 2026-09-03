import GaloisForLFunctions.HTGeometry.FirstOrderWimanTopRelationSlope
import GaloisForLFunctions.HTGeometry.LogScaleMonomialCurve

open Finset Complex Filter Topology Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- Nonzero monomials on the top value/derivative-degree face. -/
def firstOrderTopNewtonFace (S : Finset (ℕ × ℕ))
    (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) : Finset (ℕ × ℕ) :=
  S.filter fun i => i.1 + i.2 = d ∧ A i ≠ 0

/-- Logarithmic Newton weight at derivative-ratio slope `p`. -/
def firstOrderNewtonWeight (A : ℕ × ℕ → Polynomial ℂ) (p : ℝ)
    (i : ℕ × ℕ) : ℝ :=
  ((A i).natDegree : ℝ) + (i.2 : ℝ) * p

/-- Terms on the top total-degree face that attain a prescribed maximal Newton weight. -/
def firstOrderMaxNewtonFace (S : Finset (ℕ × ℕ))
    (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) (p w : ℝ) : Finset (ℕ × ℕ) :=
  (firstOrderTopNewtonFace S A d).filter fun i => firstOrderNewtonWeight A p i = w

/-- Edge polynomial formed from leading coefficients on a top Newton face. -/
def firstOrderNewtonEdgePolynomial (face : Finset (ℕ × ℕ))
    (A : ℕ × ℕ → Polynomial ℂ) : Polynomial ℂ :=
  ∑ i ∈ face, Polynomial.C (A i).leadingCoeff * Polynomial.X ^ i.2

/-- Wiman relative error transfers central-index exponent `q` to logarithmic-derivative exponent
`q - 1`. -/
theorem hasLogScaleExponent_logDerivative_of_wiman
    {y : ℕ → ℝ} {z : ℕ → ℂ} {q : ℝ}
    (hρ : Tendsto (fun n => Real.exp (y n)) atTop atTop)
    (hz : ∀ n, ‖z n‖ = Real.exp (y n))
    (hνpos : ∀ n, 0 < (centralIndex a (Real.exp (y n)) : ℝ))
    (hslope : Tendsto
      (fun n => Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) / y n)
      atTop (nhds q))
    (hdefect : Tendsto (fun n =>
      ‖z n * deriv (coeffFun a) (z n) / coeffFun a (z n) -
        (centralIndex a (Real.exp (y n)) : ℂ)‖ /
          (centralIndex a (Real.exp (y n)) : ℝ)) atTop (nhds 0)) :
    HasLogScaleExponent atTop (fun n => Real.exp (y n))
      (fun n => deriv (coeffFun a) (z n) / coeffFun a (z n)) (q - 1) := by
  let ρ : ℕ → ℝ := fun n => Real.exp (y n)
  let ν : ℕ → ℝ := fun n => (centralIndex a (ρ n) : ℝ)
  let W : ℕ → ℂ := fun n => z n * deriv (coeffFun a) (z n) / coeffFun a (z n)
  have hνexp : HasLogScaleExponent atTop ρ (fun n => (ν n : ℂ)) q := by
    constructor
    · filter_upwards with n
      have hνn : 0 < ν n := by simpa [ν, ρ] using hνpos n
      exact_mod_cast ne_of_gt hνn
    · simpa [ρ, ν, Real.log_exp] using hslope
  have hWexp : HasLogScaleExponent atTop ρ W q := by
    apply hasLogScaleExponent_of_relative_error hρ hνexp
      (Filter.Eventually.of_forall fun n => hνpos n)
      (Filter.Eventually.of_forall fun n => le_rfl)
    simpa [ρ, ν, W] using hdefect
  have hzexp : HasLogScaleExponent atTop ρ z 1 := by
    constructor
    · filter_upwards with n
      apply norm_ne_zero_iff.mp
      rw [hz n]
      exact ne_of_gt (Real.exp_pos _)
    · refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
      filter_upwards [hρ.eventually_gt_atTop 1] with n hρ1
      have hlogρ : Real.log (ρ n) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
        (lt_trans one_pos hρ1) (ne_of_gt hρ1)
      rw [hz n]
      simpa [ρ] using (div_self hlogρ).symm
  refine (hWexp.div hzexp).congr' ?_
  filter_upwards with n
  have hzne : z n ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hz n]
    exact ne_of_gt (Real.exp_pos _)
  dsimp [W]
  field_simp

/-- Every transcendental entire order-one ADE determines a genuine Newton edge at the fixed Wiman
slope: two distinct derivative powers attain the maximal weight, and their edge polynomial has a
nonzero complex root. -/
theorem exists_firstOrderWimanNewtonEdge_of_relation
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0)
    (hPrel : ∀ w : ℂ, MvPolynomial.eval
      (Fin.cons w fun j : Fin 2 => iteratedDeriv (j : ℕ) (coeffFun a) w) P = 0) :
    ∃ (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d m : ℕ)
        (y : ℕ → ℝ) (z : ℕ → ℂ) (q : ℝ) (i₁ i₂ : ℕ × ℕ) (c : ℂ),
      (∀ i ∈ S, i.1 + i.2 ≤ d) ∧
      (∀ w : ℂ,
        ∑ i ∈ S, (A i).eval w * (coeffFun a w) ^ i.1 *
          (deriv (coeffFun a) w) ^ i.2 = 0) ∧
      1 ≤ m ∧ m ≤ d ∧ (d - m, m) ∈ S ∧
      (∀ i ∈ S, i.1 + i.2 = d → i.2 ≤ m) ∧
      A (d - m, m) ≠ 0 ∧ d ≤ (A (d - m, m)).natDegree ∧
      0 < q ∧ Tendsto (fun n => Real.exp (y n)) atTop atTop ∧
      (∀ n, ‖z n‖ = Real.exp (y n)) ∧
      (∀ n, 0 < (centralIndex a (Real.exp (y n)) : ℝ)) ∧
      Tendsto (fun n => Real.log ((centralIndex a (Real.exp (y n)) : ℕ) : ℝ) / y n)
        atTop (nhds q) ∧
      Tendsto (fun n =>
        ‖∑ i ∈ S.filter (fun i => i.1 + i.2 = d),
          (A i).eval (z n) * (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ i.2‖)
        atTop (nhds 0) ∧
      Tendsto (fun n =>
        ‖z n * deriv (coeffFun a) (z n) / coeffFun a (z n) -
          (centralIndex a (Real.exp (y n)) : ℂ)‖ /
            (centralIndex a (Real.exp (y n)) : ℝ)) atTop (nhds 0) ∧
      firstOrderMvPoly S A =
        MvPolynomial.X 0 ^ d * MvPolynomial.X 2 * P ∧
      IsPositiveDerivativeCoefficientShift P S A d ∧
      i₁ ∈ firstOrderMaxNewtonFace S A d (q - 1)
        (firstOrderNewtonWeight A (q - 1) i₁) ∧
      i₂ ∈ firstOrderMaxNewtonFace S A d (q - 1)
        (firstOrderNewtonWeight A (q - 1) i₁) ∧ i₁ ≠ i₂ ∧
      firstOrderNewtonWeight A (q - 1) i₁ = firstOrderNewtonWeight A (q - 1) i₂ ∧
      (∀ i ∈ firstOrderTopNewtonFace S A d,
        firstOrderNewtonWeight A (q - 1) i ≤ firstOrderNewtonWeight A (q - 1) i₁) ∧
      c ≠ 0 ∧ (firstOrderNewtonEdgePolynomial
        (firstOrderMaxNewtonFace S A d (q - 1)
          (firstOrderNewtonWeight A (q - 1) i₁)) A).IsRoot c := by
  classical
  obtain ⟨S, A, d, m, y, z, q, hdeg, hrel, hmpos, hmle, htarget, htopdeg,
    hAne, hAdeg, hqpos, hρ, hz, hνpos, hslope, htoplim, hdefectlim, hpoly, hshift⟩ :=
      exists_firstOrderWimanTopRelationSlope_of_relation ha hn₀ htrans P hP hPrel
  let face : Finset (ℕ × ℕ) := firstOrderTopNewtonFace S A d
  let weight : ℕ × ℕ → ℝ := firstOrderNewtonWeight A (q - 1)
  have htargetFace : (d - m, m) ∈ face := by
    simpa [face, firstOrderTopNewtonFace] using And.intro htarget (And.intro (by omega) hAne)
  have hfaceNe : face.Nonempty := ⟨(d - m, m), htargetFace⟩
  obtain ⟨i₁, hi₁, hi₁max⟩ := Finset.exists_max_image face weight hfaceNe
  have htargetWeightPos : 0 < weight (d - m, m) := by
    have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
    have hmdreal : (m : ℝ) ≤ d := by exact_mod_cast hmle
    have hdegreal : (d : ℝ) ≤ (A (d - m, m)).natDegree := by exact_mod_cast hAdeg
    dsimp [weight, firstOrderNewtonWeight]
    nlinarith [hqpos]
  have hi₁pos : 0 < weight i₁ := lt_of_lt_of_le htargetWeightPos
    (hi₁max (d - m, m) htargetFace)
  have hzexp : HasLogScaleExponent atTop (fun n => Real.exp (y n)) z 1 := by
    constructor
    · filter_upwards with n
      apply norm_ne_zero_iff.mp
      rw [hz n]
      exact ne_of_gt (Real.exp_pos _)
    · refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop))
      filter_upwards [hρ.eventually_gt_atTop 1] with n hρ1
      have hlogρ : Real.log (Real.exp (y n)) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one (Real.exp_pos _) (ne_of_gt hρ1)
      rw [hz n]
      exact (div_self hlogρ).symm
  have hTexp : HasLogScaleExponent atTop (fun n => Real.exp (y n))
      (fun n => deriv (coeffFun a) (z n) / coeffFun a (z n)) (q - 1) :=
    hasLogScaleExponent_logDerivative_of_wiman hρ hz hνpos hslope hdefectlim
  have hfaceSub : face ⊆ S.filter (fun i => i.1 + i.2 = d) := by
    intro i hi
    simp only [face, firstOrderTopNewtonFace, Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨hi.1, hi.2.1⟩
  have hfaceSumEq : ∀ n,
      (∑ i ∈ face, (A i).eval (z n) *
          (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ i.2) =
        ∑ i ∈ S.filter (fun i => i.1 + i.2 = d), (A i).eval (z n) *
          (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ i.2 := by
    intro n
    rw [Finset.sum_subset hfaceSub]
    intro i hiTop hiNot
    have hAi : A i = 0 := by
      by_contra hAi
      apply hiNot
      simp only [face, firstOrderTopNewtonFace, Finset.mem_filter]
      exact ⟨(Finset.mem_filter.mp hiTop).1, (Finset.mem_filter.mp hiTop).2, hAi⟩
    rw [hAi]
    simp
  have htopzero : Tendsto (fun n =>
      ∑ i ∈ S.filter (fun i => i.1 + i.2 = d), (A i).eval (z n) *
        (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ i.2)
      atTop (nhds 0) := tendsto_zero_iff_norm_tendsto_zero.mpr htoplim
  have hfacezero : Tendsto (fun n =>
      ∑ i ∈ face, (A i).eval (z n) *
        (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ i.2)
      atTop (nhds 0) := by
    refine Tendsto.congr' ?_ htopzero
    filter_upwards with n
    exact (hfaceSumEq n).symm
  have hfaceLittle :
      (fun n => ∑ i ∈ face, (A i).eval (z n) *
        (deriv (coeffFun a) (z n) / coeffFun a (z n)) ^ i.2) =o[atTop]
          (fun _ : ℕ => (1 : ℂ)) :=
    (Asymptotics.isLittleO_one_iff ℂ).2 hfacezero
  have hAface : ∀ i ∈ face, A i ≠ 0 := by
    intro i hi
    simp only [face, firstOrderTopNewtonFace, Finset.mem_filter] at hi
    exact hi.2.2
  have hsecond : ∃ i₂ ∈ face, i₂ ≠ i₁ ∧ weight i₂ = weight i₁ := by
    by_contra hnone
    have hstrict : ∀ i ∈ face, i ≠ i₁ → weight i < weight i₁ := by
      intro i hi hine
      have hle := hi₁max i hi
      apply lt_of_le_of_ne hle
      intro heq
      exact hnone ⟨i, hi, hine, heq⟩
    have hnot := not_isLittleO_newton_sum_of_unique_max hρ hzexp hTexp
      face A Prod.snd hi₁ hAface hstrict
      (g := fun _ : ℕ => (1 : ℂ))
      (hasLogScaleExponent_const hρ (c := (1 : ℂ)) one_ne_zero) hi₁pos
    exact hnot hfaceLittle
  obtain ⟨i₂, hi₂, hi₂ne, hi₂weight⟩ := hsecond
  let maxFace : Finset (ℕ × ℕ) := face.filter fun i => weight i = weight i₁
  have hi₁MaxFace : i₁ ∈ maxFace := by
    change i₁ ∈ face.filter (fun i => weight i = weight i₁)
    exact Finset.mem_filter.mpr ⟨hi₁, rfl⟩
  have hi₂MaxFace : i₂ ∈ maxFace := by
    change i₂ ∈ face.filter (fun i => weight i = weight i₁)
    exact Finset.mem_filter.mpr ⟨hi₂, hi₂weight⟩
  have hAmaxFace : ∀ i ∈ maxFace, A i ≠ 0 := by
    intro i hi
    have hi' : i ∈ face ∧ weight i = weight i₁ := by
      simpa only [maxFace, Finset.mem_filter] using hi
    exact hAface i hi'.1
  have hsndInj : Set.InjOn Prod.snd (↑maxFace : Set (ℕ × ℕ)) := by
    intro i hi j hj hsnd
    have hi' : i ∈ S ∧ i.1 + i.2 = d ∧ A i ≠ 0 := by
      have hiMem : i ∈ maxFace := hi
      have himax : i ∈ face ∧ weight i = weight i₁ := by
        exact Finset.mem_filter.mp (show i ∈ face.filter (fun k => weight k = weight i₁) by
          exact hiMem)
      have hitop : i ∈ face := himax.1
      simpa [face, firstOrderTopNewtonFace] using hitop
    have hj' : j ∈ S ∧ j.1 + j.2 = d ∧ A j ≠ 0 := by
      have hjMem : j ∈ maxFace := hj
      have hjmax : j ∈ face ∧ weight j = weight i₁ := by
        exact Finset.mem_filter.mp (show j ∈ face.filter (fun k => weight k = weight i₁) by
          exact hjMem)
      have hjtop : j ∈ face := hjmax.1
      simpa [face, firstOrderTopNewtonFace] using hjtop
    change i.2 = j.2 at hsnd
    apply Prod.ext
    · omega
    · exact hsnd
  obtain ⟨c, hcne, hcroot⟩ :=
    exists_ne_zero_isRoot_edge maxFace A Prod.snd hAmaxFace hsndInj
      hi₁MaxFace hi₂MaxFace hi₂ne.symm
  refine ⟨S, A, d, m, y, z, q, i₁, i₂, c, hdeg, hrel, hmpos, hmle, htarget,
    htopdeg, hAne, hAdeg, hqpos, hρ, hz, hνpos, hslope, htoplim, hdefectlim,
    hpoly, hshift, ?_, ?_, hi₂ne.symm, ?_, hi₁max, hcne, ?_⟩
  · simpa [firstOrderMaxNewtonFace, maxFace, face, weight] using hi₁MaxFace
  · simpa [firstOrderMaxNewtonFace, maxFace, face, weight] using hi₂MaxFace
  · exact hi₂weight.symm
  · simpa [firstOrderNewtonEdgePolynomial, firstOrderMaxNewtonFace, maxFace, face, weight]
      using hcroot

end

end GaloisForLFunctions.HTGeometry
