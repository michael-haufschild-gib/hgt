import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectPairKernel
import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrades

/-!
# Positive curvature-defect cumulant cooling in the complete theta source

Literal point-and-ray pair moments satisfy the coupled binary kernel bound.
Two countable-sum transports absorb the binary cumulant grade. The checked
higher-grade estimates, spectral reserve, and actual theta tail probability
then give strict positivity of the complete cumulant cooling functional.
The final identity differentiates the exact logarithmic defect ratio.
-/

namespace RHTower.ThetaCuspDefect
open scoped BigOperators
noncomputable section
def bareMoment (q d : ℝ) (j : ℕ) : ℝ :=
  (d+1)*d^j+(3/2)*d*∑ i ∈ Finset.range (j+1),
    (j.choose i:ℝ)*d^(j-i)*(i.factorial:ℝ)/q^(i+1)
def momentConvolution (m n : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*m i*n (j-i)

theorem atomMoment_eq_bare {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) (j : ℕ) :
    atomMoment n q j =
      Real.exp (-(3/2)*thetaCuspLikelihoodGap n)*Real.exp (-q*thetaCuspLikelihoodGap n)*
        (thetaCuspLikelihoodGap n+1)*bareMoment q (thetaCuspLikelihoodGap n) j := by
  unfold atomMoment
  rw [integral_pow_mul_exp_neg_thetaCuspAtomLikelihoodSpectralMeasure hn j hq]
  have hn2 : (n:ℝ)^2 = thetaCuspLikelihoodGap n+1 := by
    unfold thetaCuspLikelihoodGap
    ring
  have hn4 : (n:ℝ)^4 = (thetaCuspLikelihoodGap n+1)^2 := by
    calc (n:ℝ)^4 = ((n:ℝ)^2)^2 := by ring
         _ = _ := by rw [hn2]
  rw [hn4,hn2]
  unfold bareMoment
  simp only [neg_mul]
  ring

private theorem bare_pair_moment_2 (d e : ℝ) {q : ℝ} (hq : 0 < q) :
    momentConvolution (bareMoment q d) (bareMoment q e) 2 =
      pairMomentNumerator q (d+e) (d*e) 2/q^4 := by
  norm_num [momentConvolution, bareMoment, Finset.sum_range_succ, Nat.choose, Nat.factorial,
    pairMomentNumerator, rayMoment, doubleRayMoment]
  field_simp [hq.ne']
  ring

private theorem bare_pair_moment_3 (d e : ℝ) {q : ℝ} (hq : 0 < q) :
    momentConvolution (bareMoment q d) (bareMoment q e) 3 =
      pairMomentNumerator q (d+e) (d*e) 3/q^5 := by
  norm_num [momentConvolution, bareMoment, Finset.sum_range_succ, Nat.choose, Nat.factorial,
    pairMomentNumerator, rayMoment, doubleRayMoment]
  field_simp [hq.ne']
  ring

private theorem bare_pair_moment_4 (d e : ℝ) {q : ℝ} (hq : 0 < q) :
    momentConvolution (bareMoment q d) (bareMoment q e) 4 =
      pairMomentNumerator q (d+e) (d*e) 4/q^6 := by
  norm_num [momentConvolution, bareMoment, Finset.sum_range_succ, Nat.choose, Nat.factorial,
    pairMomentNumerator, rayMoment, doubleRayMoment]
  field_simp [hq.ne']
  ring

private theorem bare_pair_moment_5 (d e : ℝ) {q : ℝ} (hq : 0 < q) :
    momentConvolution (bareMoment q d) (bareMoment q e) 5 =
      pairMomentNumerator q (d+e) (d*e) 5/q^7 := by
  norm_num [momentConvolution, bareMoment, Finset.sum_range_succ, Nat.choose, Nat.factorial,
    pairMomentNumerator, rayMoment, doubleRayMoment]
  field_simp [hq.ne']
  ring

private theorem bare_pair_moment_6 (d e : ℝ) {q : ℝ} (hq : 0 < q) :
    momentConvolution (bareMoment q d) (bareMoment q e) 6 =
      pairMomentNumerator q (d+e) (d*e) 6/q^8 := by
  norm_num [momentConvolution, bareMoment, Finset.sum_range_succ, Nat.choose, Nat.factorial,
    pairMomentNumerator, rayMoment, doubleRayMoment]
  field_simp [hq.ne']
  ring

theorem bare_pair_cooling_eq (d e : ℝ) {q : ℝ} (hq : 0 < q) :
    coolingFunctional q (momentConvolution (bareMoment q d) (bareMoment q e)) =
      pairCoolingKernel q d e/q^8 := by
  simp only [coolingFunctional,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd,coolingCoefficient]
  rw [bare_pair_moment_2 d e hq,bare_pair_moment_3 d e hq,bare_pair_moment_4 d e hq,
    bare_pair_moment_5 d e hq,bare_pair_moment_6 d e hq]
  unfold pairCoolingKernel
  field_simp [hq.ne']
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section
def pairCooling (q : ℝ) (m n : ℕ → ℝ) : ℝ :=
  coolingFunctional q (momentConvolution m n)

theorem hasSum_pairCooling_left (q : ℝ) (n : ℕ → ℝ)
    {f : ℕ → ℕ → ℝ} {m : ℕ → ℝ}
    (hf : ∀ j, HasSum (fun k => f k j) (m j)) :
    HasSum (fun k => pairCooling q (f k) n) (pairCooling q m n) := by
  have hj (j : ℕ) : HasSum (fun k => momentConvolution (f k) n j)
      (momentConvolution m n j) := by
    have h := hasSum_sum (s := Finset.range (j+1))
      (fun i _ => ((hf i).mul_right (n (j-i))).mul_left (j.choose i:ℝ))
    simpa only [momentConvolution,mul_assoc] using h
  unfold pairCooling coolingFunctional
  exact hasSum_sum (fun j _ => (hj (j+2)).mul_left _)

theorem hasSum_pairCooling_right (q : ℝ) (m : ℕ → ℝ)
    {f : ℕ → ℕ → ℝ} {n : ℕ → ℝ}
    (hf : ∀ j, HasSum (fun k => f k j) (n j)) :
    HasSum (fun k => pairCooling q m (f k)) (pairCooling q m n) := by
  have hj (j : ℕ) : HasSum (fun k => momentConvolution m (f k) j)
      (momentConvolution m n j) := by
    exact hasSum_sum (fun i _ => (hf (j-i)).mul_left ((j.choose i:ℝ)*m i))
  unfold pairCooling coolingFunctional
  exact hasSum_sum (fun j _ => (hj (j+2)).mul_left _)

theorem pairCooling_self (q : ℝ) (m : ℕ → ℝ) :
    pairCooling q m m = 2*m 0*coolingFunctional q m+2*gradeTwo q m := by
  simp only [pairCooling,coolingFunctional,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num only [Nat.reduceAdd,momentConvolution,Finset.sum_range_succ,
    Finset.sum_range_zero,Nat.choose,Nat.reduceSub,Nat.factorial]
  unfold gradeTwo
  ring

theorem gradeTwo_normalized_eq (q : ℝ) :
    gradeTwo q (thetaCuspLikelihoodNormalizedMoment q) =
      gradeTwo q (thetaCuspHigherLikelihoodSpectralMoment q)/(thetaCuspLikelihoodPartition q)^2 := by
  unfold gradeTwo thetaCuspLikelihoodNormalizedMoment
  ring
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section

theorem coolingFunctional_mul (q a : ℝ) (m : ℕ → ℝ) :
    coolingFunctional q (fun j => a*m j) = a*coolingFunctional q m := by
  unfold coolingFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem momentConvolution_mul (a b : ℝ) (m n : ℕ → ℝ) (j : ℕ) :
    momentConvolution (fun i => a*m i) (fun i => b*n i) j =
      (a*b)*momentConvolution m n j := by
  unfold momentConvolution
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pairCooling_mul (q a b : ℝ) (m n : ℕ → ℝ) :
    pairCooling q (fun j => a*m j) (fun j => b*n j) = (a*b)*pairCooling q m n := by
  unfold pairCooling
  have hfun : momentConvolution (fun i => a*m i) (fun i => b*n i) =
      fun j => (a*b)*momentConvolution m n j := by
    funext j
    exact momentConvolution_mul a b m n j
  rw [hfun]
  exact coolingFunctional_mul q (a*b) _

theorem bareMoment_zero (d : ℝ) {q : ℝ} (hq : 0 < q) :
    bareMoment q d 0 = massNumerator q d/q := by
  norm_num [bareMoment,Finset.sum_range_succ,Nat.choose,Nat.factorial,massNumerator]
  field_simp [hq.ne']

def atomScale (n : ℕ) (q : ℝ) : ℝ :=
  Real.exp (-(3/2)*thetaCuspLikelihoodGap n)*Real.exp (-q*thetaCuspLikelihoodGap n)*
    (thetaCuspLikelihoodGap n+1)

theorem atom_pairCooling_eq {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    {q : ℝ} (hq : 0 < q) :
    pairCooling q (atomMoment n q) (atomMoment m q) =
      (atomScale n q*atomScale m q)*
        (pairCoolingKernel q (thetaCuspLikelihoodGap n) (thetaCuspLikelihoodGap m)/q^8) := by
  have hfn : atomMoment n q = fun j => atomScale n q*bareMoment q (thetaCuspLikelihoodGap n) j := by
    funext j
    exact atomMoment_eq_bare hn hq j
  have hfm : atomMoment m q = fun j => atomScale m q*bareMoment q (thetaCuspLikelihoodGap m) j := by
    funext j
    exact atomMoment_eq_bare hm hq j
  rw [hfn,hfm,pairCooling_mul]
  exact congrArg (fun z => (atomScale n q*atomScale m q)*z)
    (bare_pair_cooling_eq (thetaCuspLikelihoodGap n) (thetaCuspLikelihoodGap m) hq)

theorem atom_pairCooling_le {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    {q : ℝ} (hq : 3/2 ≤ q) :
    pairCooling q (atomMoment n q) (atomMoment m q) ≤
      384*(coolingFunctional q (atomMoment n q)*atomMoment m q 0+
        atomMoment n q 0*coolingFunctional q (atomMoment m q)) := by
  have hq0 : 0 < q := by linarith
  have hd (k : ℕ) (hk : 2 ≤ k) : 3 ≤ thetaCuspLikelihoodGap k := by
    unfold thetaCuspLikelihoodGap
    have hkr : (2:ℝ) ≤ k := by exact_mod_cast hk
    nlinarith
  have hn0 : 0 ≤ atomScale n q := by
    have h := hd n hn
    unfold atomScale
    positivity
  have hm0 : 0 ≤ atomScale m q := by
    have h := hd m hm
    unfold atomScale
    positivity
  have hs (k : ℕ) (hk : 2 ≤ k) :
      coolingFunctional q (atomMoment k q) =
        atomScale k q*thetaCuspLikelihoodGap k/q^6*
          normalizedDefectCoolingKernel q (thetaCuspLikelihoodGap k) :=
    atom_coolingFunctional_eq hk hq0
  have hz (k : ℕ) (hk : 2 ≤ k) :
      atomMoment k q 0 = atomScale k q*massNumerator q (thetaCuspLikelihoodGap k)/q := by
    rw [atomMoment_eq_bare hk hq0,bareMoment_zero _ hq0]
    unfold atomScale
    ring
  rw [atom_pairCooling_eq hn hm hq0,hs n hn,hs m hm,hz n hn,hz m hm]
  have h := mul_le_mul_of_nonneg_left (pairCoolingKernel_fusion hq (hd n hn) (hd m hm))
    (show 0 ≤ atomScale n q*atomScale m q/q^8 by positivity)
  calc
    _ = (atomScale n q*atomScale m q/q^8)*
        pairCoolingKernel q (thetaCuspLikelihoodGap n) (thetaCuspLikelihoodGap m) := by ring
    _ ≤ _ := h
    _ = _ := by field_simp [hq0.ne']
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section

theorem full_pairCooling_le {q : ℝ} (hq : 3/2 ≤ q) :
    pairCooling q (thetaCuspHigherLikelihoodSpectralMoment q)
      (thetaCuspHigherLikelihoodSpectralMoment q) ≤
      768*thetaCuspHigherLikelihoodSpectralMoment q 0*
        coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q) := by
  have hq0 : 0 < q := by linarith
  let M := thetaCuspHigherLikelihoodSpectralMoment q
  have hm (j : ℕ) : HasSum (fun n : ℕ => atomMoment (n+2) q j) (M j) :=
    hasSum_atomMoment hq0 j
  have hs := hasSum_atomCooling hq0
  have hfixed (n : ℕ) :
      pairCooling q (atomMoment (n+2) q) M ≤
        384*(coolingFunctional q (atomMoment (n+2) q)*M 0+
          atomMoment (n+2) q 0*coolingFunctional q M) := by
    have hl := hasSum_pairCooling_right q (atomMoment (n+2) q) hm
    have hr := (((hm 0).mul_left (coolingFunctional q (atomMoment (n+2) q))).add
      (hs.mul_left (atomMoment (n+2) q 0))).mul_left 384
    exact hasSum_le (fun m => atom_pairCooling_le (by omega) (by omega) hq) hl hr
  have hl := hasSum_pairCooling_left q M hm
  have hr := ((hs.mul_right (M 0)).add ((hm 0).mul_right (coolingFunctional q M))).mul_left 384
  calc
    _ ≤ 384*(coolingFunctional q M*M 0+M 0*coolingFunctional q M) :=
      hasSum_le hfixed hl hr
    _ = _ := by dsimp only [M]; ring

theorem gradeTwo_ordinary_le {q : ℝ} (hq : 3/2 ≤ q) :
    gradeTwo q (thetaCuspHigherLikelihoodSpectralMoment q) ≤
      383*thetaCuspHigherLikelihoodSpectralMoment q 0*
        coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q) := by
  have h := full_pairCooling_le hq
  rw [pairCooling_self] at h
  nlinarith only [h]

theorem gradeTwo_normalized_le {q : ℝ} (hq : 3/2 ≤ q) :
    gradeTwo q (thetaCuspLikelihoodNormalizedMoment q) ≤
      383*thetaCuspLikelihoodTailProbability q*
        coolingFunctional q (thetaCuspLikelihoodNormalizedMoment q) := by
  have hq0 : 0 < q := by linarith
  rw [gradeTwo_normalized_eq,cooling_normalized_eq]
  unfold thetaCuspLikelihoodTailProbability thetaCuspLikelihoodNormalizedMoment
  rw [show 383*(thetaCuspHigherLikelihoodSpectralMoment q 0/thetaCuspLikelihoodPartition q)*
      (coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q)/thetaCuspLikelihoodPartition q) =
      (383*thetaCuspHigherLikelihoodSpectralMoment q 0*
        coolingFunctional q (thetaCuspHigherLikelihoodSpectralMoment q))/
          (thetaCuspLikelihoodPartition q)^2 by ring]
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos (thetaCuspLikelihoodPartition_pos hq0))).2
    (gradeTwo_ordinary_le hq)
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section

theorem source_cooling_cumulant_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < coolingFunctional (thetaCuspLikelihoodCoordinate x)
      (likelihoodCumulant (thetaCuspLikelihoodCoordinate x)) := by
  let q := thetaCuspLikelihoodCoordinate x
  have hq : 3/2 ≤ q := by
    have he := Real.one_le_exp hx
    have he2 : 1 ≤ (Real.exp x)^2 := by nlinarith [Real.exp_pos x]
    have hpi := le_mul_of_one_le_right Real.pi_pos.le he2
    dsimp only [q,thetaCuspLikelihoodCoordinate]
    linarith [Real.pi_gt_d2]
  have hq0 : 0 < q := by linarith
  let p := thetaCuspLikelihoodTailProbability q
  let S := coolingFunctional q (thetaCuspLikelihoodNormalizedMoment q)
  let T := coolingCoefficient q 6*thetaCuspLikelihoodNormalizedMoment q 6
  let C := 402*p^3+120*p^5
  have hp : 0 ≤ p :=
    div_nonneg (thetaCuspHigherLikelihoodSpectralMoment_nonneg 0)
      (thetaCuspLikelihoodPartition_pos hq0).le
  have hp400 : 400*p < 1 :=
    four_hundred_mul_thetaCuspLikelihoodTailProbability_coordinate_lt_one hx
  have hp1 : p < (1/400:ℝ) := by linarith
  have hp3 : p^3 ≤ (1/400:ℝ)^3 := by gcongr
  have hp5 : p^5 ≤ (1/400:ℝ)^5 := by gcongr
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hS : 0 < S := by
    dsimp only [S]
    rw [cooling_normalized_eq]
    exact div_pos (full_coolingFunctional_pos hq) (thetaCuspLikelihoodPartition_pos hq0)
  have hres : T ≤ 1000*S := normalized_cooling_reserve hq
  have hcost : C*T ≤ C*(1000*S) := mul_le_mul_of_nonneg_left hres hC
  have hpair : gradeTwo q (thetaCuspLikelihoodNormalizedMoment q) ≤ 383*p*S :=
    gradeTwo_normalized_le hq
  have hlow : S-gradeTwo q (thetaCuspLikelihoodNormalizedMoment q)-C*T ≤
      coolingFunctional q (likelihoodCumulant q) := by
    simpa only [S,C,T,p,mul_assoc] using cooling_cumulant_lower_pair hq
  have hdelta : 0 < 1-383*p-1000*C := by
    dsimp only [C]
    norm_num at hp3 hp5
    nlinarith only [hp1,hp3,hp5]
  have hgood := mul_pos hdelta hS
  change 0 < coolingFunctional q (likelihoodCumulant q)
  nlinarith only [hcost,hpair,hlow,hgood]
end
end RHTower.ThetaCuspDefect

namespace RHTower.ThetaCuspDefect
noncomputable section
def logarithmicDefectRatio (q : ℝ) : ℝ :=
  q^5/(27*(q+3))*((q+3/2)^3*thetaCuspLikelihoodFifthCumulant q-
    10*(q+3/2)^2*thetaCuspLikelihoodFourthCumulant q+
    24*(q+3/2)*thetaCuspLikelihoodThirdCumulant q-
    12*thetaCuspLikelihoodVariance q)

theorem hasDerivAt_logarithmicDefectRatio {q : ℝ} (hq : 0 < q) :
    HasDerivAt logarithmicDefectRatio
      (-q^4/(27*(q+3)^2)*coolingFunctional q (likelihoodCumulant q)) q := by
  have ha := (hasDerivAt_id q).add_const (3/2:ℝ)
  have h2 := hasDerivAt_thetaCuspLikelihoodVariance hq
  have h3 := hasDerivAt_thetaCuspLikelihoodThirdCumulant hq
  have h4 := hasDerivAt_thetaCuspLikelihoodFourthCumulant hq
  have h5 := hasDerivAt_thetaCuspLikelihoodFifthCumulant hq
  have h0 := ((ha.pow 3).mul h5).sub (((ha.pow 2).mul h4).const_mul 10)
  have h1 := h0.add ((ha.mul h3).const_mul 24)
  have hk := h1.sub (h2.const_mul 12)
  have hq3 : 27*(q+3) ≠ 0 := by positivity
  have hw := ((hasDerivAt_id q).pow 5).div
    (((hasDerivAt_id q).add_const (3:ℝ)).const_mul 27) hq3
  convert! hw.mul hk using 1
  · funext y
    dsimp [logarithmicDefectRatio]
    ring
  · simp only [Pi.pow_apply,Pi.mul_apply,Pi.div_apply,Pi.add_apply,Pi.sub_apply,id_eq,
      Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one]
    simp only [coolingFunctional,Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
    norm_num only [Nat.reduceAdd,coolingCoefficient,likelihoodCumulant]
    have hn : q+3 ≠ 0 := by positivity
    field_simp [hn]
    ring
end
end RHTower.ThetaCuspDefect
