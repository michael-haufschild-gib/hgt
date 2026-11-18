import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervalsAsymptotic
import GaloisForLFunctions.RHTower.WeilLagLocalWorkHuxley
import GaloisForLFunctions.RHTower.FreeLagSymbolBoundaryLayer
import GaloisForLFunctions.RHTower.Sieve.CharacterWindowMass
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Two-sided bounds for every future prime increment

The relative exceptional measure for a single multiplicative window decreases faster
than any inverse power of log X. It therefore pays for a geometric grid of
window sizes at once. Monotonicity interpolates both signs between grid points.
The critical-window endpoint map expands distances, so pulling its exceptional
set back to the same centers preserves the vanishing relative cost.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open _root_.RHTower

private def badPrimeWindow (X η r : ℝ) : Set ℝ :=
  Icc X (2*X) ∩ {u | η*(r*u) < |Chebyshev.psi (u+r*u)-Chebyshev.psi u-r*u|}

private theorem measurable_badPrimeWindow (X η r : ℝ) : MeasurableSet (badPrimeWindow X η r) := by
  have h : Measurable (fun u : ℝ => Chebyshev.psi (u+r*u)) := Chebyshev.psi_mono.measurable.comp (by fun_prop)
  exact measurableSet_Icc.inter (measurableSet_lt (by fun_prop)
    (((h.sub Chebyshev.psi_mono.measurable).sub (measurable_const.mul measurable_id)).abs))

/-- A single exceptional-volume majorant for every exponent above α.
One log factor is reserved to sum over the window sizes. -/
private theorem uniform_prime_window_exception {α η : ℝ} (hα : 1/6 < α) (hα' : α < 1)
    (hη : 0 < η) (hη' : η ≤ 1) :
    ∃ E : ℝ → ℝ, (∀ X ≥ 1, 0 ≤ E X) ∧
      Tendsto (fun X : ℝ => (Real.log X+2)*E X) atTop (𝓝 0) ∧
      ∀ᶠ X : ℝ in atTop, ∀ θ : ℝ, α ≤ θ → X^(θ-1) ≤ 1/2 →
        volume.real (badPrimeWindow X η (X^(θ-1))) ≤ X*E X := by
  let c := 192/(5*η)
  let D := 25600/η^2*(64*(|xiLineTwoLogDerivConstant|+2))
  let Z := fun (X θ : ℝ) => ∑' q : XiZeroCopy, zeroShortWeight (X^2)
    (c*(X^2)^(2*((1-θ)/2))) (q.1:ℂ)
  let E := fun X : ℝ => D*((Real.log (X^2)+2)^2*Z X α)
  have hc : 1 ≤ c := by dsimp only [c]; rw [le_div_iff₀ (by positivity)]; linarith only [hη']
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hZ (X θ : ℝ) : 0 ≤ Z X θ := tsum_nonneg fun q => zeroShortWeight_nonneg (sq_nonneg _) (by
    exact mul_nonneg (zero_le_one.trans hc) (Real.rpow_nonneg (sq_nonneg _) _)) _
  have hE (X : ℝ) : 0 ≤ E X := mul_nonneg hD (mul_nonneg (sq_nonneg _) (hZ ..))
  have hlim := (tendsto_logPow_mul_tsum_zeroShortWeight_seven_twelfths 3
    (u := (1-α)/2) (by linarith only [hα']) (by linarith only [hα]) hc).comp
    (tendsto_pow_atTop (two_ne_zero : (2:ℕ) ≠ 0))
  have hbig := (tendsto_rpow_atTop (show 0 < 2*α by linarith only [hα])).eventually_ge_atTop
    (16*(64+1152*xiSpectralThreeHalvesMass)/η^2)
  refine ⟨E,fun X _ => hE X,?_,?_⟩
  · have hl := hlim.const_mul D
    rw [mul_zero] at hl
    apply squeeze_zero' _ _ hl
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
      exact mul_nonneg (by linarith only [Real.log_nonneg hX]) (hE X)
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
      have hlog : Real.log X+2 ≤ Real.log (X^2)+2 := by
        rw [Real.log_pow, Nat.cast_ofNat]; linarith only [Real.log_nonneg hX]
      calc (Real.log X+2)*E X ≤ (Real.log (X^2)+2)*E X := mul_le_mul_of_nonneg_right hlog (hE _)
           _ = D*((Real.log (X^2)+2)^3*Z X α) := by dsimp only [E]; ring
  · filter_upwards [eventually_ge_atTop (4:ℝ),hbig] with X hX hlarge
    intro θ hθ hr
    have h1 : 1 ≤ X := by linarith only [hX]
    have hs : 1 ≤ X^2 := one_le_pow₀ h1
    have hpow := Real.rpow_le_rpow_of_exponent_le h1 (show 2*α ≤ 2*θ by linarith only [hθ])
    have hbig' : 16*(64+1152*xiSpectralThreeHalvesMass) ≤ η^2*X^(2*θ) := by
      rw [div_le_iff₀ (sq_pos_of_pos hη)] at hlarge
      calc _ ≤ X^(2*α)*η^2 := hlarge
           _ ≤ _ := (mul_le_mul_of_nonneg_right hpow (sq_nonneg _)).trans_eq (mul_comm ..)
    have hv := volume_psi_short_asymptotic_le hη hη' hX hr hbig'
    have hz : Z X θ ≤ Z X α := tsum_zeroShortWeight_mono hs (mul_nonneg (zero_le_one.trans hc)
      (Real.rpow_nonneg (sq_nonneg _) _)) (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hθ])) (zero_le_one.trans hc))
    have harmon := almostAllHarmonicWeight_le h1
    change volume.real (badPrimeWindow X η (X^(θ-1))) ≤ 25600/η^2*almostAllHarmonicWeight X*X*Z X θ at hv
    apply hv.trans
    calc _ ≤ 25600/η^2*(64*(|xiLineTwoLogDerivConstant|+2)*(Real.log (X^2)+2)^2)*X*Z X α := by
             apply mul_le_mul _ hz (hZ ..) (by positivity)
             exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left harmon (by positivity)) (by linarith only [hX])
         _ = X*E X := by dsimp only [E,D]; ring

private def prefixGridRadius (X α ρ : ℝ) (k : ℕ) := X^(α-1)*ρ^k

private def prefixGridSize (X ρ : ℝ) := ⌈Real.log X/Real.log ρ⌉₊ + 2

private def prefixGridBad (X α η ρ : ℝ) : Set ℝ :=
  ⋃ k ∈ Finset.range (prefixGridSize X ρ),
    if prefixGridRadius X α ρ k ≤ 1/2 then badPrimeWindow X η (prefixGridRadius X α ρ k) else ∅

private theorem measurable_prefixGridBad (X α η ρ : ℝ) : MeasurableSet (prefixGridBad X α η ρ) := by
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro _
  split_ifs <;> first | exact measurable_badPrimeWindow .. | exact MeasurableSet.empty

private theorem prefixGridBad_subset (X α η ρ : ℝ) : prefixGridBad X α η ρ ⊆ Icc X (2*X) := by
  intro u hu
  obtain ⟨k,hk⟩ := Set.mem_iUnion.1 hu
  obtain ⟨_,hw⟩ := Set.mem_iUnion.1 hk
  split_ifs at hw
  · exact hw.1
  · exact hw.elim

private theorem tendsto_prefixGridBad {α η ρ : ℝ} (hα : 1/6 < α) (hα' : α < 1)
    (hη : 0 < η) (hη' : η ≤ 1) (hρ : 1 < ρ) :
    Tendsto (fun X : ℝ => volume.real (prefixGridBad X α η ρ)/X) atTop (𝓝 0) := by
  obtain ⟨E,hE,hl,hlarge⟩ := uniform_prime_window_exception hα hα' hη hη'
  have hd := Real.log_pos hρ
  let D := (Real.log ρ)⁻¹+3
  have hlim := hl.const_mul D
  rw [mul_zero] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact div_nonneg ENNReal.toReal_nonneg hX.le
  · filter_upwards [hlarge,eventually_gt_atTop (1:ℝ)] with X hb hX
    have hX0 := zero_lt_one.trans hX
    have hx := Real.log_pos hX
    let S := Finset.range (prefixGridSize X ρ)
    let A := fun k => if prefixGridRadius X α ρ k ≤ 1/2 then badPrimeWindow X η (prefixGridRadius X α ρ k) else ∅
    have hexc (k : ℕ) : volume.real (A k) ≤ X*E X := by
      dsimp only [A]; split_ifs with hr
      · let θ := α+(k:ℝ)*Real.log ρ/Real.log X
        have hθ : α ≤ θ := le_add_of_nonneg_right (by positivity)
        have heq : X^(θ-1) = prefixGridRadius X α ρ k := by
          rw [prefixGridRadius,Real.rpow_def_of_pos hX0,Real.rpow_def_of_pos hX0,
            show Real.log X*(θ-1) = Real.log X*(α-1)+(k:ℝ)*Real.log ρ by
              dsimp only [θ]; field_simp [hx.ne']; ring,Real.exp_add,Real.exp_nat_mul,
            Real.exp_log (zero_lt_one.trans hρ)]
        rw [← heq] at hr ⊢
        exact hb θ hθ hr
      · simpa only [measureReal_empty] using mul_nonneg hX0.le (hE X hX.le)
    have hm := (measureReal_biUnion_finset_le (μ := volume) S A).trans
      (Finset.sum_le_sum (fun k _ => hexc k))
    have hcard : (S.card:ℝ) ≤ D*(Real.log X+2) := by
      simp only [S,Finset.card_range,prefixGridSize,Nat.cast_add,Nat.cast_ofNat]
      have hh := (Nat.ceil_lt_add_one (div_nonneg hx.le hd.le)).le
      dsimp only [D]
      rw [div_eq_mul_inv] at hh ⊢
      nlinarith only [hh,hx.le,inv_nonneg.mpr hd.le]
    change volume.real (⋃ k ∈ S, A k) / X ≤ _
    rw [div_le_iff₀ hX0]
    calc _ ≤ (S.card:ℝ)*(X*E X) := by simpa only [Finset.sum_const,nsmul_eq_mul] using hm
         _ ≤ (D*(Real.log X+2))*(X*E X) := mul_le_mul_of_nonneg_right hcard (mul_nonneg hX0.le (hE X hX.le))
         _ = _ := by ring


/-- Every relative length from the first grid radius through one quarter
lies between consecutive retained radii. -/
private theorem prefixGrid_bracket {X α ρ r : ℝ} (hX : 1 < X) (hα : 0 ≤ α)
    (hρ : 1 < ρ) (hρ' : ρ ≤ 2) (hd : X^(α-1) ≤ r) (hr : r ≤ 1/4) :
    ∃ k : ℕ, k+1 < prefixGridSize X ρ ∧ prefixGridRadius X α ρ k ≤ r ∧
      r ≤ prefixGridRadius X α ρ (k+1) ∧ prefixGridRadius X α ρ (k+1) ≤ 1/2 := by
  let d := X^(α-1)
  have hX0 := zero_lt_one.trans hX
  have hd0 : 0 < d := Real.rpow_pos_of_pos hX0 _
  have hρ0 := zero_lt_one.trans hρ
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near ((one_le_div hd0).2 hd) hρ
  have hk : d*ρ^k ≤ r := by simpa only [mul_comm d] using (le_div_iff₀ hd0).1 hlo
  have hk' : r ≤ d*ρ^(k+1) := by simpa only [mul_comm d] using ((div_lt_iff₀ hd0).1 hhi).le
  have hdx : 1 ≤ d*X := by
    dsimp only [d]; rw [← Real.rpow_add_one hX0.ne', sub_add_cancel]
    exact Real.one_le_rpow hX.le hα
  have hpow : ρ^k ≤ X := hlo.trans ((div_le_iff₀ hd0).2 (by
    rw [mul_comm X d]; linarith only [hr,hdx]))
  have hlog := Real.log_le_log (pow_pos hρ0 k) hpow
  rw [Real.log_pow] at hlog
  have hkn := ((le_div_iff₀ (Real.log_pos hρ)).2 hlog).trans (Nat.le_ceil _)
  have hkn' : k ≤ ⌈Real.log X/Real.log ρ⌉₊ := by exact_mod_cast hkn
  refine ⟨k,by dsimp only [prefixGridSize]; omega,hk,hk',?_⟩
  change d*ρ^(k+1) ≤ (1/2:ℝ)
  rw [pow_succ,← mul_assoc]
  exact (mul_le_mul hk hρ' hρ0.le (hd0.le.trans hd)).trans (by linarith only [hr])

/-- Except on a set of relative measure tending to zero, every future
Chebyshev increment lies in a two-sided cone of prescribed slope, with
an additive error at any fixed power above one sixth. -/
theorem two_sided_all_future_prime_prefixes {α ε : ℝ} (hα : 1/6 < α) (hα' : α < 1)
    (hε : 0 < ε) :
    ∃ bad : ℝ → Set ℝ, (∀ X, MeasurableSet (bad X) ∧ bad X ⊆ Icc X (2*X)) ∧
      Tendsto (fun X : ℝ => volume.real (bad X)/X) atTop (𝓝 0) ∧
      ∀ᶠ X : ℝ in atTop, ∀ u ∈ Icc X (2*X), u ∉ bad X → ∀ y ≥ u,
        |Chebyshev.psi y-Chebyshev.psi u-(y-u)| ≤ ε*(y-u)+4*X^α := by
  let η := min ε 1 / 8
  let ρ := 1+η
  have hη : 0 < η := div_pos (lt_min hε zero_lt_one) (by norm_num)
  have hη1 : η ≤ 1/8 := by dsimp only [η]; linarith only [min_le_right ε 1]
  have hηε : 8*η ≤ ε := by dsimp only [η]; linarith only [min_le_left ε 1]
  have hη' : η ≤ 1 := by linarith only [hη1]
  have hρ : 1 < ρ := by dsimp only [ρ]; linarith only [hη]
  have hρ2 : ρ ≤ 2 := by dsimp only [ρ]; linarith only [hη']
  refine ⟨fun X => prefixGridBad X α η ρ,fun _ => ⟨measurable_prefixGridBad ..,prefixGridBad_subset ..⟩,
    tendsto_prefixGridBad hα hα' hη hη' hρ,?_⟩
  have hdsmall := (tendsto_rpow_neg_atTop (sub_pos.mpr hα')).eventually_lt_const (by norm_num : (0:ℝ)<1/4)
  have hp := _root_.RHTower.FreeLagTrace.tendsto_psi_div.eventually
    (Metric.ball_mem_nhds 1 (div_pos hε (by norm_num : (0:ℝ)<9)))
  obtain ⟨V,hV⟩ := eventually_atTop.mp hp
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop V,hdsmall] with X hX hXV hdS
  intro u hu hgood y hy
  have hX0 := zero_lt_one.trans hX
  have hu0 := hX0.trans_le hu.1
  have hscale := Real.rpow_pos_of_pos hX0 α
  have hΔ := sub_nonneg.mpr hy
  have hpsum := Chebyshev.psi_mono hy
  have hmain (v : ℝ) (hv : X ≤ v) : |Chebyshev.psi v-v| ≤ (ε/9)*v := by
    have h := hV v (hXV.trans hv)
    change dist (Chebyshev.psi v/v) 1 < ε/9 at h
    rw [Real.dist_eq, show Chebyshev.psi v/v-1=(Chebyshev.psi v-v)/v by
      field_simp [(hX0.trans_le hv).ne'],abs_div,abs_of_pos (hX0.trans_le hv)] at h
    exact ((div_lt_iff₀ (hX0.trans_le hv)).1 h).le
  by_cases hfar : u/4 ≤ y-u
  · have heq : Chebyshev.psi y-Chebyshev.psi u-(y-u) = (Chebyshev.psi y-y)-(Chebyshev.psi u-u) := by ring
    rw [heq]
    calc _ ≤ _ := (abs_sub ..).trans (add_le_add (hmain y (hu.1.trans hy)) (hmain u hu.1))
         _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hfar hε.le,hscale.le]
  let r := (y-u)/u
  have hr : r ≤ 1/4 := (div_le_iff₀ hu0).2 (by linarith only [lt_of_not_ge hfar])
  have hru : r*u = y-u := div_mul_cancel₀ _ hu0.ne'
  let d := X^(α-1)
  have hd0 : 0 < d := Real.rpow_pos_of_pos hX0 _
  have hd1 : d ≤ 1/4 := by simpa only [neg_sub] using hdS.le
  have hprice : d*X = X^α := by dsimp only [d]; rw [← Real.rpow_add_one hX0.ne',sub_add_cancel]
  have grid (k : ℕ) (hk : k < prefixGridSize X ρ) (hkr : prefixGridRadius X α ρ k ≤ 1/2) :
      let s := prefixGridRadius X α ρ k
      (1-η)*(s*u) ≤ Chebyshev.psi (u+s*u)-Chebyshev.psi u ∧
        Chebyshev.psi (u+s*u)-Chebyshev.psi u ≤ (1+η)*(s*u) := by
    have hn : u ∉ badPrimeWindow X η (prefixGridRadius X α ρ k) := by
      intro hf
      apply hgood
      exact Set.mem_iUnion.2 ⟨k,Set.mem_iUnion.2 ⟨Finset.mem_range.2 hk,by simpa only [if_pos hkr] using hf⟩⟩
    have hle : |Chebyshev.psi (u+prefixGridRadius X α ρ k*u)-Chebyshev.psi u-
        prefixGridRadius X α ρ k*u| ≤ η*(prefixGridRadius X α ρ k*u) := le_of_not_gt fun h => hn ⟨hu,h⟩
    obtain ⟨h1,h2⟩ := abs_le.mp hle
    constructor <;> linarith only [h1,h2]
  by_cases hsmall : r ≤ d
  · have hk := grid 0 (by dsimp only [prefixGridSize]; omega) (by
      simpa only [prefixGridRadius,pow_zero,mul_one] using (hd1.trans (by norm_num : (1/4:ℝ) ≤ 1/2)))
    simp only [prefixGridRadius,pow_zero,mul_one] at hk
    have hyn : y ≤ u+d*u := by linarith only [mul_le_mul_of_nonneg_right hsmall hu0.le,hru]
    have hdu : d*u ≤ 2*X^α := by
      calc _ ≤ d*(2*X) := mul_le_mul_of_nonneg_left hu.2 hd0.le
           _ = _ := by rw [← hprice]; ring
    have hupper := (sub_le_sub_right (Chebyshev.psi_mono hyn) (Chebyshev.psi u)).trans hk.2
    have hsum : (1+η)*(d*u) ≤ 4*X^α := (mul_le_mul (by linarith only [hη'] : 1+η ≤ 2)
      hdu (mul_nonneg hd0.le hu0.le) (by norm_num)).trans_eq (by ring)
    apply abs_le.2
    constructor <;> linarith only [hupper,hsum,hpsum,mul_le_mul_of_nonneg_right hsmall hu0.le,hru,
      hdu,hscale.le,hΔ,mul_nonneg hε.le hΔ]
  · obtain ⟨k,hk,hlo,hhi,hcap⟩ := prefixGrid_bracket hX (by linarith only [hα]) hρ hρ2
      (le_of_not_ge hsmall) hr
    let s := prefixGridRadius X α ρ k
    have hs0 : 0 < s := mul_pos hd0 (pow_pos (zero_lt_one.trans hρ) _)
    have hstep : prefixGridRadius X α ρ (k+1) = s*ρ := by dsimp only [prefixGridRadius,s]; rw [pow_succ,mul_assoc]
    have hg1 := (grid k (by omega) (hlo.trans (hr.trans (by norm_num)))).1
    have hg2 := (grid (k+1) hk hcap).2
    rw [hstep] at hhi hg2
    have hleft : u+s*u ≤ y := by linarith only [mul_le_mul_of_nonneg_right hlo hu0.le,hru]
    have hright : y ≤ u+(s*ρ)*u := by linarith only [mul_le_mul_of_nonneg_right hhi hu0.le,hru]
    have hl := hg1.trans (sub_le_sub_right (Chebyshev.psi_mono hleft) _)
    have hh := (sub_le_sub_right (Chebyshev.psi_mono hright) _).trans hg2
    have hupper : (1+η)*ρ ≤ 1+ε := by
      dsimp only [ρ]
      nlinarith only [hηε,hη.le,mul_le_mul_of_nonneg_right hη' hη.le]
    have hcoef : ρ-(1-η) ≤ ε := by dsimp only [ρ]; linarith only [hηε,hη]
    have hsu := mul_nonneg hs0.le hu0.le
    have heu : ε*(s*u) ≤ ε*(y-u) := by rw [← hru]; gcongr
    apply abs_le.2
    constructor
    · have hlen : y-u ≤ (s*u)*ρ := calc
        _ = r*u := hru.symm
        _ ≤ (s*ρ)*u := mul_le_mul_of_nonneg_right hhi hu0.le
        _ = _ := mul_right_comm ..
      change (1-η)*(s*u) ≤ _ at hl
      nlinarith only [hl,hlen,mul_le_mul_of_nonneg_right hcoef hsu,heu,hscale.le]
    · have hprice' : (1+η)*((s*ρ)*u) ≤ (1+ε)*(y-u) := calc
        _ = ((1+η)*ρ)*(s*u) := by ring
        _ ≤ (1+ε)*(r*u) := mul_le_mul hupper (mul_le_mul_of_nonneg_right hlo hu0.le) hsu (by linarith only [hε])
        _ = _ := by rw [hru]
      linarith only [hh,hprice',hscale.le]

/-- The right endpoint of the critical-width interval on the arithmetic axis. -/
def criticalPrimeWindowEnd (u : ℝ) := u+Real.sqrt (u*Real.log u)

private theorem measurable_criticalPrimeWindowEnd : Measurable criticalPrimeWindowEnd := by
  unfold criticalPrimeWindowEnd
  fun_prop

/-- Pulling an exceptional set back to the original centers cannot enlarge its
measure. The derivative of the endpoint map is at least one. -/
private theorem volume_preimage_criticalPrimeWindowEnd {X : ℝ} (hX : 1 < X)
    {B : Set ℝ} (hm : MeasurableSet B) :
    volume (Icc X (2*X) ∩ (criticalPrimeWindowEnd ⁻¹' B)) ≤ volume B := by
  let A := Icc X (2*X) ∩ (criticalPrimeWindowEnd ⁻¹' B)
  have hA : MeasurableSet A := measurableSet_Icc.inter (hm.preimage measurable_criticalPrimeWindowEnd)
  let d := fun u : ℝ => 1+(Real.log u+1)/(2*Real.sqrt (u*Real.log u))
  have hd (u : ℝ) (hu : u ∈ A) : HasDerivWithinAt criticalPrimeWindowEnd (d u) A u := by
    have hu1 := hX.trans_le hu.1.1
    have hu0 := zero_lt_one.trans hu1
    have hp := (Real.hasDerivAt_mul_log hu0.ne').sqrt (mul_pos hu0 (Real.log_pos hu1)).ne'
    simpa only [criticalPrimeWindowEnd,d,Pi.add_apply,id_eq] using!
      ((hasDerivAt_id' u).add hp).hasDerivWithinAt (s := A)
  have hexpand (u : ℝ) (hu : u ∈ A) : 1 ≤ d u := by
    have hlog := Real.log_nonneg (hX.trans_le hu.1.1).le
    dsimp only [d]; exact le_add_of_nonneg_right (div_nonneg (by linarith only [hlog]) (by positivity))
  have hmono : StrictMonoOn criticalPrimeWindowEnd A := by
    intro u hu v hv huv
    have hu1 := hX.trans_le hu.1.1
    have hl := Real.log_le_log (zero_lt_one.trans hu1) huv.le
    exact add_lt_add_of_lt_of_le huv (Real.sqrt_le_sqrt (mul_le_mul huv.le hl
      (Real.log_nonneg hu1.le) (zero_lt_one.trans (hu1.trans huv)).le))
  have harea := lintegral_image_eq_lintegral_abs_deriv_mul hA hd hmono.injOn (fun _ => 1)
  simp only [setLIntegral_one,mul_one] at harea
  calc volume A = ∫⁻ _ in A, (1:ℝ≥0∞) := (setLIntegral_one A).symm
       _ ≤ ∫⁻ u in A, ENNReal.ofReal |d u| := setLIntegral_mono' hA fun u hu => by
         rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((hexpand u hu).trans (le_abs_self _))
       _ = volume (criticalPrimeWindowEnd '' A) := harea.symm
       _ ≤ volume B := measure_mono (by rintro _ ⟨u,hu,rfl⟩; exact hu.2)

/-- Replacing length by the number of integers in a real interval costs at
most one at its two endpoints together. -/
private theorem centered_integer_prefix_le {u y M : ℝ} (hu : 0 ≤ u) (hy : u ≤ y)
    (h : |Chebyshev.psi y-Chebyshev.psi u-(y-u)| ≤ M) :
    |∑ n ∈ Finset.Ioc ⌊u⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1)| ≤ M+1 := by
  rw [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,Nat.card_Ioc,
    Nat.cast_sub (Nat.floor_mono hy),← _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc hy]
  obtain ⟨hlo,hhi⟩ := abs_le.1 h
  apply abs_le.2
  constructor <;> linarith only [hlo,hhi,Nat.floor_le hu,Nat.floor_le (hu.trans hy),
    Nat.lt_floor_add_one y,Nat.lt_floor_add_one u]

/-- The same exceptional set handles all integer endpoints from the center
and from its moving far edge. Both signed prefixes include the full integer
reference. Any positive-density set of prescribed centers can be intersected
with its complement at vanishing relative cost. -/
theorem two_sided_prefixes_from_both_critical_endpoints {α ε : ℝ}
    (hα : 1/6 < α) (hα' : α < 1) (hε : 0 < ε) :
    ∃ bad : ℝ → Set ℝ, (∀ X, MeasurableSet (bad X) ∧ bad X ⊆ Icc X (2*X)) ∧
      Tendsto (fun X : ℝ => volume.real (bad X)/X) atTop (𝓝 0) ∧
      ∀ᶠ X : ℝ in atTop, ∀ u ∈ Icc X (2*X), u ∉ bad X →
        ∀ z ∈ ({u,criticalPrimeWindowEnd u} : Set ℝ), ∀ y ≥ z,
          |∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1)| ≤
            ε*(y-z)+4*(2*X)^α+1 := by
  obtain ⟨B,hm,hsmall,hall⟩ := two_sided_all_future_prime_prefixes hα hα' hε
  let A := fun X : ℝ => Icc X (2*X) ∩ (criticalPrimeWindowEnd ⁻¹' (B X ∪ B (2*X)))
  let bad := fun X : ℝ => B X ∪ A X
  have hA (X : ℝ) : MeasurableSet (A X) := measurableSet_Icc.inter
    (((hm X).1.union (hm (2*X)).1).preimage measurable_criticalPrimeWindowEnd)
  have hdbl := tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2)
  have h2 := hsmall.comp hdbl
  refine ⟨bad,fun X => ⟨(hm X).1.union (hA X),union_subset (hm X).2 inter_subset_left⟩,?_,?_⟩
  · have hl := (hsmall.const_mul 2).add (h2.const_mul 2)
    simp only [mul_zero,add_zero] at hl
    apply squeeze_zero' _ _ hl
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
      exact div_nonneg ENNReal.toReal_nonneg hX.le
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
      have hX0 := zero_lt_one.trans hX
      have hfin (v : ℝ) : volume (B v) ≠ ⊤ :=
        measure_ne_top_of_subset (hm v).2 (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      have hf := measure_union_lt_top (hfin X).lt_top (hfin (2*X)).lt_top
      have hpre := volume_preimage_criticalPrimeWindowEnd hX ((hm X).1.union (hm (2*X)).1)
      have hbound : volume.real (A X) ≤ volume.real (B X)+volume.real (B (2*X)) :=
        (ENNReal.toReal_mono hf.ne hpre).trans (measureReal_union_le ..)
      calc volume.real (bad X)/X ≤ (volume.real (B X)+(volume.real (B X)+volume.real (B (2*X))))/X :=
             div_le_div_of_nonneg_right ((measureReal_union_le ..).trans (add_le_add le_rfl hbound)) hX0.le
           _ = 2*(volume.real (B X)/X)+2*(volume.real (B (2*X))/(2*X)) := by field_simp; ring
  · filter_upwards [hall,hdbl.eventually hall,eventually_gt_atTop (1:ℝ)] with X hx h2x hX
    intro u hu hgood z hz y hy
    have hu1 := hX.trans_le hu.1
    have hu0 := zero_lt_one.trans hu1
    have hX0 := zero_lt_one.trans hX
    have huB : u ∉ B X := fun h => hgood (Or.inl h)
    have heB : criticalPrimeWindowEnd u ∉ B X ∪ B (2*X) := fun h => hgood (Or.inr ⟨hu,h⟩)
    have hpow := Real.rpow_le_rpow hX0.le (by linarith only [hX0] : X ≤ 2*X) (by linarith only [hα])
    have hsize : u ≤ criticalPrimeWindowEnd u := le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have htop : criticalPrimeWindowEnd u ≤ 2*(2*X) := by
      have hlog := Real.log_le_sub_one_of_pos hu0
      have hroot : Real.sqrt (u*Real.log u) ≤ u := (Real.sqrt_le_iff).2
        ⟨hu0.le, by nlinarith only [mul_le_mul_of_nonneg_left hlog hu0.le,hu0.le]⟩
      unfold criticalPrimeWindowEnd; linarith only [hroot,hu.2]
    rcases Set.mem_insert_iff.mp hz with hzu | hz
    · subst z
      exact (centered_integer_prefix_le hu0.le hy (hx u hu huB y hy)).trans (by linarith only [hpow])
    · rw [Set.mem_singleton_iff] at hz
      subst z
      apply centered_integer_prefix_le (hu0.le.trans hsize) hy
      by_cases hcut : criticalPrimeWindowEnd u ≤ 2*X
      · exact (hx _ ⟨hu.1.trans hsize,hcut⟩ (fun h => heB (Or.inl h)) y hy).trans (by linarith only [hpow])
      · exact h2x _ ⟨(lt_of_not_ge hcut).le,htop⟩ (fun h => heB (Or.inr h)) y hy

/-- Both endpoints retain a prescribed set of centers up to any fixed relative
loss, uniformly in the choice of that measurable set. -/
theorem two_sided_prefixes_on_prescribed_centers {α ε δ : ℝ}
    (hα : 1/6 < α) (hα' : α < 1) (hε : 0 < ε) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, ∀ A : Set ℝ, MeasurableSet A → A ⊆ Icc X (2*X) →
      ∃ G : Set ℝ, MeasurableSet G ∧ G ⊆ A ∧ volume.real A-δ*X ≤ volume.real G ∧
        ∀ u ∈ G, ∀ z ∈ ({u,criticalPrimeWindowEnd u} : Set ℝ), ∀ y ≥ z,
          |∑ n ∈ Finset.Ioc ⌊z⌋₊ ⌊y⌋₊, (ArithmeticFunction.vonMangoldt n-1)| ≤
            ε*(y-z)+4*(2*X)^α+1 := by
  obtain ⟨bad,hm,hsmall,hall⟩ := two_sided_prefixes_from_both_critical_endpoints hα hα' hε
  filter_upwards [hall,hsmall.eventually_lt_const hδ,eventually_gt_atTop (0:ℝ)] with X hx hv hX
  intro A hA hAI
  have hf : volume (bad X) ≠ ⊤ := measure_ne_top_of_subset (hm X).2
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  refine ⟨A \ bad X,hA.diff (hm X).1,sdiff_subset,?_,fun u hu => hx u (hAI hu.1) hu.2⟩
  exact (sub_le_sub_left ((div_lt_iff₀ hX).1 hv).le _).trans (le_measureReal_sdiff hf)

#print axioms two_sided_prefixes_on_prescribed_centers
#print axioms two_sided_prefixes_from_both_critical_endpoints
#print axioms two_sided_all_future_prime_prefixes
end GaloisForLFunctions.ExclusionOfTheCriticalState
