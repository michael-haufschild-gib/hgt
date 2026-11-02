import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineConeWindowCosts
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineTailEstimates

/-!
# Exact spline corrections on a late tail

Supergeometric coefficient masses absorb the geometric costs of finite
interpolation. A sufficiently late tail admits every correction, has summable
coefficient norm, and places each block above its cumulative atom count.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

lemma gridPrefixSize_shift_le (n : ℕ → ℕ) (s k : ℕ) :
    gridPrefixSize (fun j => n (s+j)) k ≤ gridPrefixSize n (s+k) := by
  unfold gridPrefixSize
  conv_rhs => rw [show s+k+1=s+(k+1) by omega,sum_range_add]
  dsimp only
  omega

/-- A schedule of exact spline corrections with summable norms and sparse heights. -/
structure PrescribedSplineSchedule (a b d D : ℝ) where
  cutoff : ℝ
  start : ℕ
  size : ℕ → ℕ
  height : ℕ → ℝ
  span : ℕ → ℝ
  cutoff_one : 1 ≤ cutoff
  cutoff_tail : 8 ≤ ((D-d)/2*min a b)*cutoff
  size_pos : ∀ k, 0 < size k
  height_one : ∀ k, 1 ≤ height k
  span_pos : ∀ k, 0 < span k
  span_le_height : ∀ k, span k ≤ height k
  prefix_le_height : ∀ k, (gridPrefixSize size k : ℝ) ≤ height k
  height_eq : ∀ k, height k=massRadius (2*correctionMass (start+k)) (size k)
  mass_le : ∀ k, splineNumeratorEnvelope D*correctionMass (start+k) ≤ (1/2 : ℝ)^k
  correct : ∀ k,
    ∀ r : (coneSquare a b (quantitativeCutoff cutoff (start+k))) → ℂ,
      (∀ u, ‖r u‖ ≤ 2*(correctionMass (start+k))^2) →
      ∃ γ : Fin (size k) → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc (height k) (height k+span k)) ∧
        ∀ u : (coneSquare a b (quantitativeCutoff cutoff (start+k))),
          (∑ j, splineMomentCoefficient ((approachLevel d D (start+k) : ℂ)+
            (γ j : ℂ)*Complex.I)*phase u.val (γ j))=r u

/-- A concrete late-tail schedule supplies exact unit-multiplicity corrections
at the prescribed eighth-power height, with summable norm and sparse support. -/
theorem exists_two_prime_spline_tail_schedule {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D : ℝ}
    (hd : 0 < d) (hdD : d < D) :
    Nonempty (PrescribedSplineSchedule (Real.log p) (Real.log q) d D) := by
  classical
  have ha : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hb : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  let c := (D-d)/2*min (Real.log p) (Real.log q)
  have hc : 0 < c := mul_pos (half_pos (sub_pos.mpr hdD)) (lt_min ha hb)
  let C := 1+8/c
  have hC : 1 ≤ C := by
    dsimp only [C]
    linarith only [div_pos (by norm_num : (0 : ℝ) < 8) hc]
  have hcutoff : 8 ≤ c*C := by
    dsimp only [C]
    have he : c*(8/c)=8 := by field_simp [hc.ne']
    nlinarith only [hc,he]
  obtain ⟨U,R,hU,hR,hfinite⟩ := exists_two_prime_spline_geometric_corrections hp hq hpq hd hdD hC
  have hδd (k : ℕ) : d ≤ approachLevel d D k := approachLevel_lower hdD k
  have hδD (k : ℕ) : approachLevel d D k ≤ D := (approachLevel_lt hdD k).le
  choose n span H₀ ε hn hspan hH₀ hε hnU hspanU hHU hεU hrealize using
    fun k => hfinite k (approachLevel d D k) (hδd k) (hδD k)
  let F := fun k : ℕ => (1+3*U)*(4*R)^k
  have hRp : 0 < R := lt_trans zero_lt_one hR
  have hF0 (k : ℕ) : 0 ≤ F k := by dsimp only [F]; positivity
  have hFbound (k : ℕ) : 1+H₀ k+span k+(gridPrefixSize n k : ℝ) ≤ F k := by
    have hpow : R^k ≤ (4*R)^k := pow_le_pow_left₀ hRp.le (by nlinarith only [hRp]) k
    have hH := (hHU k).trans (mul_le_mul_of_nonneg_left hpow hU.le)
    have hs := (hspanU k).trans (mul_le_mul_of_nonneg_left hpow hU.le)
    have hpref := gridPrefixSize_geometric_bound hU.le hR.le hnU k
    have hone : (1 : ℝ) ≤ (4*R)^k := one_le_pow₀ (by nlinarith only [hR])
    dsimp only [F]
    nlinarith only [hH,hs,hpref,hone]
  have hheight := eventually_le_matched_spline_height hn hF0 (by positivity : 0 < 4*R)
    (fun _ => le_rfl : ∀ k, F k ≤ (1+3*U)*(4*R)^k)
  have hradius := eventually_two_mass_le_radius hε hRp hεU
  have hmasslim : Tendsto (fun k : ℕ => splineNumeratorEnvelope D*(1/2 : ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).const_mul (splineNumeratorEnvelope D)
  have hmass := hmasslim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨start,hstart⟩ := eventually_atTop.1 (hheight.and (hradius.and hmass))
  let size := fun k => n (start+k)
  let height := fun k => massRadius (2*correctionMass (start+k)) (size k)
  have hdata : ∀ k : ℕ, 0 < size k ∧ 1 ≤ height k ∧ 0 < span (start+k) ∧
      span (start+k) ≤ height k ∧ (gridPrefixSize size k : ℝ) ≤ height k ∧
      splineNumeratorEnvelope D*correctionMass (start+k) ≤ (1/2 : ℝ)^k := by
    intro k
    have htail := hstart (start+k) (by omega)
    have hdom := (hFbound (start+k)).trans htail.1
    have hnpref : (0 : ℝ) ≤ gridPrefixSize n (start+k) := Nat.cast_nonneg _
    have hH0 := hH₀ (start+k)
    have hs0 := hspan (start+k)
    have hheight0 : 1 ≤ height k := by dsimp only [height,size]; linarith only [hdom,hH0,hs0,hnpref]
    have hspH : span (start+k) ≤ height k := by dsimp only [height,size]; linarith only [hdom,hH0,hnpref]
    have hprefH : (gridPrefixSize size k : ℝ) ≤ height k := by
      have hshift : (gridPrefixSize size k : ℝ) ≤ gridPrefixSize n (start+k) := by
        dsimp only [size]
        exact_mod_cast gridPrefixSize_shift_le n start k
      dsimp only [height,size]
      linarith only [hdom,hH0,hs0,hshift]
    have hmassK : splineNumeratorEnvelope D*correctionMass (start+k) ≤ (1/2 : ℝ)^k := by
      calc
        _ ≤ splineNumeratorEnvelope D*(1/2 : ℝ)^(start+k) :=
          mul_le_mul_of_nonneg_left (correctionMass_le_geometric (start+k))
            (splineNumeratorEnvelope_nonneg D)
        _ = (splineNumeratorEnvelope D*(1/2 : ℝ)^start)*(1/2 : ℝ)^k := by rw [pow_add]; ring
        _ ≤ 1*(1/2 : ℝ)^k := mul_le_mul_of_nonneg_right
          (hstart start le_rfl).2.2.le (by positivity)
        _ = _ := one_mul _
    exact ⟨hn _,hheight0,hspan _,hspH,hprefH,hmassK⟩
  refine ⟨{
    cutoff := C
    start := start
    size := size
    height := height
    span := fun k => span (start+k)
    cutoff_one := hC
    cutoff_tail := hcutoff
    size_pos := fun k => (hdata k).1
    height_one := fun k => (hdata k).2.1
    span_pos := fun k => (hdata k).2.2.1
    span_le_height := fun k => (hdata k).2.2.2.1
    prefix_le_height := fun k => (hdata k).2.2.2.2.1
    height_eq := fun _ => rfl
    mass_le := fun k => (hdata k).2.2.2.2.2
    correct := ?_
  }⟩
  intro k r hr
  have htail := hstart (start+k) (by omega)
  have hdom := (hFbound (start+k)).trans htail.1
  have hnpref : (0 : ℝ) ≤ gridPrefixSize n (start+k) := Nat.cast_nonneg _
  have hs0 := hspan (start+k)
  have hthreshold : H₀ (start+k) ≤ height k := by
    dsimp only [height,size]
    linarith only [hdom,hs0,hnpref]
  apply hrealize (start+k) (height k) hthreshold r
  intro u
  have hpow : (height k)^8=(size k : ℝ)/correctionMass (start+k) :=
    matched_spline_height_pow (correctionMass_pos _) (hn _)
  have hbudget : ε (start+k)*(size k : ℝ)/(height k)^8=
      ε (start+k)*correctionMass (start+k) := by
    rw [hpow]
    have hnR : (0 : ℝ) < size k := by
      dsimp only [size]
      exact_mod_cast hn (start+k)
    field_simp [hnR.ne',(correctionMass_pos (start+k)).ne']
  rw [hbudget]
  exact (hr u).trans (by
    have hh := mul_le_mul_of_nonneg_right htail.2.1 (correctionMass_pos (start+k)).le
    nlinarith only [hh])

#print axioms exists_two_prime_spline_tail_schedule
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
