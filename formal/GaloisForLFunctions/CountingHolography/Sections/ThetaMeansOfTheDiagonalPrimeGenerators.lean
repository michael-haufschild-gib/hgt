import GaloisForLFunctions.CountingHolography.Sections.TheThetaMeanOfTheSquareTrace
import GaloisForLFunctions.CountingHolography.Sections.TheSignedDegreeAtTheNearestUpperSquare
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionSpectralEscape

/-!
# Theta averages of the actual diagonal section generators

At every logarithmic center, assign each theta mass element to the nearest
upper integer square. The two long trace translates have zero theta mean.
Only the bounded short lag survives in the limiting degree. The ordinary
log generator divided by n² consequently has bounded translated mean.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open MeasureTheory Filter Topology Finset ArithmeticScatteringHolography
open RenormalizedIntersectionTheory _root_.RHTower

private abbrev Q (n : ℕ) := integerProbe _ (successorSquareTriple n)
private abbrev phi := thetaCuspFullSource
private abbrev mass := ∫ x : ℝ, phi x
private abbrev residue := 6*realSplineTrace 0-4*realSplineTrace (Real.log 4)

/-- Normalized theta average of an arithmetic quantity on integer squares. -/
def thetaSquareMean (g : ℕ → ℝ) (T : ℝ) : ℝ :=
  (∫ x : ℝ, thetaCuspFullSource x*g (upperSquareIndex (T+x)))/(∫ x : ℝ, thetaCuspFullSource x)

private theorem sample_measurable (g : ℕ → ℝ) : Measurable (fun u => g (upperSquareIndex u)) :=
  (measurable_of_countable g).comp upperSquareIndex_monotone.measurable

private theorem theta_integrable : Integrable phi := by
  simpa only [zero_mul,Real.exp_zero,one_mul] using HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource 0

/-- A bounded defect at late centers is uniformly integrable after every
translation to the right. On the left tail all sampled indices stay bounded. -/
private theorem translated_defect_bound (g : ℕ → ℝ) {b : ℝ}
    (h : Tendsto (fun u => g (upperSquareIndex u)-squareLongTrace u) atTop (𝓝 b)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {T : ℝ}, 0 ≤ T → ∀ x : ℝ,
      |g (upperSquareIndex (T+x))-squareLongTrace (T+x)| ≤ A*Real.exp (1/2*|x|) := by
  obtain ⟨U,hU⟩ := eventually_atTop.mp (h.abs.eventually_le_const (lt_add_one |b|))
  obtain ⟨B,hB,hF⟩ := squareLongTrace_bound
  let D := ∑ n ∈ range (upperSquareIndex U+1), |g n|
  have hD : 0 ≤ D := sum_nonneg fun _ _ => abs_nonneg _
  let K := Real.exp (1/2*|U|)
  let A := |b|+1+D+B*K
  have hA : 0 ≤ A := by dsimp only [A,K]; positivity
  refine ⟨A,hA,fun {T} hT x => ?_⟩
  have h₁ : 1 ≤ Real.exp (1/2*|x|) := Real.one_le_exp (by positivity)
  by_cases hu : U ≤ T+x
  · refine (hU _ hu).trans ((show |b|+1 ≤ A by dsimp only [A,K]; linarith only [hD,mul_nonneg hB (Real.exp_pos (1/2*|U|)).le]).trans
      (le_mul_of_one_le_right hA h₁))
  have hn : upperSquareIndex (T+x) ≤ upperSquareIndex U := upperSquareIndex_monotone (le_of_not_ge hu)
  have hg : |g (upperSquareIndex (T+x))| ≤ D := single_le_sum (f := fun n => |g n|)
    (fun _ _ => abs_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le hn))
  have ht : |T+x| ≤ |U|+|x| := abs_le.mpr ⟨by linarith only [hT,neg_abs_le x,abs_nonneg U],
    by linarith only [le_of_not_ge hu,le_abs_self U,abs_nonneg x]⟩
  have hf := (hF (T+x)).trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 1/2))) hB)
  rw [mul_add,Real.exp_add] at hf
  have hh := abs_sub_le (g (upperSquareIndex (T+x))) 0 (squareLongTrace (T+x))
  simp only [sub_zero,zero_sub,abs_neg] at hh
  dsimp only [A,K]
  linarith only [hh,hf,hg,le_mul_of_one_le_right hD h₁,
    mul_nonneg (show 0 ≤ |b|+1 by positivity) (Real.exp_pos (1/2*|x|)).le]

private theorem theta_mean_of_defect_limit (g : ℕ → ℝ) {b : ℝ}
    (h : Tendsto (fun u => g (upperSquareIndex u)-squareLongTrace u) atTop (𝓝 b)) :
    (∀ T : ℝ, 0 ≤ T → Integrable (fun x => phi x*g (upperSquareIndex (T+x)))) ∧
      Tendsto (thetaSquareMean g) atTop (𝓝 b) := by
  obtain ⟨A,_,hA⟩ := translated_defect_bound g h
  let E := fun T x : ℝ => phi x*(g (upperSquareIndex (T+x))-squareLongTrace (T+x))
  let H := fun x : ℝ => A*(Real.exp (1/2*|x|)*phi x)
  have hi : Integrable H := (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource (1/2)).const_mul A
  have hm (T : ℝ) : AEStronglyMeasurable (E T) volume :=
    (contDiff_thetaCuspFullSource.continuous.measurable.mul
      (((sample_measurable g).sub continuous_squareLongTrace.measurable).comp (measurable_const.add measurable_id))).aestronglyMeasurable
  have hb {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : ‖E T x‖ ≤ H x := by
    dsimp only [E,H]
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (thetaCuspFullSource_pos x)]
    exact (mul_le_mul_of_nonneg_left (hA hT x) (thetaCuspFullSource_pos x).le).trans_eq (by ring)
  have hE {T : ℝ} (hT : 0 ≤ T) : Integrable (E T) := hi.mono' (hm T) (Eventually.of_forall (hb hT))
  have hs (T x : ℝ) : phi x*g (upperSquareIndex (T+x)) = E T x+phi x*squareLongTrace (T+x) := by
    dsimp only [E]; ring
  refine ⟨fun T hT => by simp_rw [hs]; exact (hE hT).add (thetaMean_squareLongTrace T).1,?_⟩
  have ht : Tendsto (fun T => ∫ x, E T x) atTop (𝓝 (∫ x : ℝ, phi x*b)) :=
    tendsto_integral_filter_of_dominated_convergence H (Eventually.of_forall hm)
      ((eventually_ge_atTop 0).mono fun T hT => Eventually.of_forall (hb hT)) hi
      (Eventually.of_forall fun x => (h.comp (tendsto_atTop_add_const_right atTop x tendsto_id)).const_mul (phi x))
  rw [integral_mul_const] at ht
  have hlim := ht.div_const mass
  rw [show mass*b/mass=b by field_simp [integral_thetaCuspFullSource_pos.ne']] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 0] with T hT
  unfold thetaSquareMean
  simp_rw [hs]
  rw [integral_add (hE hT) (thetaMean_squareLongTrace T).1,(thetaMean_squareLongTrace T).2,add_zero]

/-- The normalized signed degree has a fixed mean at every translated
scale in the limit. Both growing long lags disappear exactly under theta. -/
theorem tendsto_thetaSquareMean_signed_degree :
    Tendsto (thetaSquareMean fun n => integerProbe _ (successorSquareTriple n)) atTop
      (𝓝 (6*realSplineTrace 0-4*realSplineTrace (Real.log 4))) :=
  (theta_mean_of_defect_limit Q upperSquareIndex_signed_degree).2

/-- At the original diagonal multiplicity, the normalized full surplus
with its ordinary floor loss removed has the very same limiting mean. -/
theorem tendsto_thetaSquareMean_corrected_surplus :
    Tendsto (thetaSquareMean fun n => let a := n • successorSquareTriple n
      (radius a-Real.log (generator a:ℝ)-ordinaryFloorLoss a)/(n:ℝ)^2) atTop
      (𝓝 (6*realSplineTrace 0-4*realSplineTrace (Real.log 4))) := by
  let g := fun n : ℕ => let a := n • successorSquareTriple n
    (radius a-Real.log (generator a:ℝ)-ordinaryFloorLoss a)/(n:ℝ)^2
  apply (theta_mean_of_defect_limit g ?_).2
  have h := (diagonal_full_surplus_recovers_signed_degree.comp tendsto_upperSquareIndex).add upperSquareIndex_signed_degree
  rw [zero_add] at h
  exact h.congr fun u => by change (g _-Q _)+(Q _-squareLongTrace u)=g _-squareLongTrace u; ring

private abbrev logRatio (n : ℕ) :=
  Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)/(n:ℝ)^2

private theorem ratio_discrepancy : ∃ B : ℝ, 0 ≤ B ∧ ∀ {n : ℕ}, 0 < n → |logRatio n+Q n| ≤ B := by
  obtain ⟨A,hA,hp⟩ := successorSquare_contact_degree
  obtain ⟨C,hC,hg⟩ := successorSquare_contact_error
  refine ⟨C+A,add_nonneg hC hA,fun {n} hn => ?_⟩
  let P := ordinaryPrimeContact (successorSquareTriple n)
  have hs : 0 < (n:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr hn)
  have hh : |logRatio n-P| ≤ C := by
    rw [show logRatio n-P = (Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)-
      (n:ℝ)^2*P)/(n:ℝ)^2 by unfold logRatio; field_simp,abs_div,abs_of_pos hs]
    exact (div_le_iff₀ hs).mpr (hg hn le_rfl)
  have he := add_le_add hh (hp hn)
  exact (le_of_eq (congrArg abs (show logRatio n+Q n=(logRatio n-P)+(P+Q n) by ring))).trans
    ((abs_add_le _ _).trans he)

/-- The signed log of the actual ordinary prime generator divided by n²
has uniformly bounded theta mean at every sufficiently late logarithmic
center. Bounds apply to the mean with its original signs. -/
theorem eventually_bounded_thetaSquareMean_diagonal_prime_generator :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop,
      Integrable (fun x : ℝ => let n := upperSquareIndex (T+x)
        thetaCuspFullSource x*(Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)/(n:ℝ)^2)) ∧
      |thetaSquareMean (fun n => Real.log (ordinaryPrimeGenerator
        (n • successorSquareTriple n):ℝ)/(n:ℝ)^2) T| ≤ C := by
  obtain ⟨B,hB,hq⟩ := ratio_discrepancy
  obtain ⟨hQi,hQ⟩ := theta_mean_of_defect_limit Q upperSquareIndex_signed_degree
  refine ⟨B+|residue|+1,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop 0,hQ.abs.eventually_le_const (lt_add_one |residue|)] with T hT hmean
  let F := fun x : ℝ => phi x*(logRatio (upperSquareIndex (T+x))+Q (upperSquareIndex (T+x)))
  have hF (x : ℝ) : |F x| ≤ B*phi x := by
    dsimp only [F]
    rw [abs_mul,abs_of_pos (thetaCuspFullSource_pos x),mul_comm B]
    exact mul_le_mul_of_nonneg_left (hq (upperSquareIndex_pos _)) (thetaCuspFullSource_pos x).le
  have hi : Integrable F := (theta_integrable.const_mul B).mono'
    (contDiff_thetaCuspFullSource.continuous.measurable.mul
      ((sample_measurable (fun n => logRatio n+Q n)).comp (measurable_const.add measurable_id))).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hF x)
  have he := (abs_integral_le_integral_abs (μ := volume)).trans (integral_mono hi.abs (theta_integrable.const_mul B) hF)
  rw [integral_const_mul] at he
  have hf : |(∫ x, F x)/mass| ≤ B := by
    rw [abs_div,abs_of_pos integral_thetaCuspFullSource_pos]
    exact (div_le_iff₀ integral_thetaCuspFullSource_pos).mpr he
  have hpoint (x : ℝ) : F x-phi x*Q (upperSquareIndex (T+x))=phi x*logRatio (upperSquareIndex (T+x)) := by
    dsimp only [F]; ring
  refine ⟨(hi.sub (hQi T hT)).congr (Eventually.of_forall hpoint),?_⟩
  have hsplit : thetaSquareMean logRatio T = (∫ x, F x)/mass-thetaSquareMean Q T := by
    unfold thetaSquareMean
    rw [← sub_div,← integral_sub hi (hQi T hT)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => (hpoint x).symm)
  change |thetaSquareMean logRatio T| ≤ _
  rw [hsplit]
  have ht := abs_sub_le ((∫ x, F x)/mass) 0 (thetaSquareMean Q T)
  simp only [sub_zero,zero_sub,abs_neg] at ht
  linarith only [ht,hf,hmean]

#print axioms tendsto_thetaSquareMean_signed_degree
#print axioms tendsto_thetaSquareMean_corrected_surplus
#print axioms eventually_bounded_thetaSquareMean_diagonal_prime_generator

end GaloisForLFunctions.CountingHolography.Sections
