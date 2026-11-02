import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineConeCosts
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineBlockSeparation
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SplineCorrectionSchedule

/-!
# Separated sparse spline corrections

A late tail absorbs every geometric interpolation cost into the prescribed
spline masses. Corrections retain at most three nodes per unit interval,
and successive height blocks have gaps longer than one.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Exact spline corrections retain a three-node unit count, and successive
height blocks are separated by more than one. -/
structure SparsePrescribedSplineSchedule (a b d D : ℝ) where
  base : PrescribedSplineSchedule a b d D
  block_gap : ∀ k, base.height k+base.span k+1 < base.height (k+1)
  correct_sparse : ∀ k,
    ∀ r : (coneSquare a b (quantitativeCutoff base.cutoff (base.start+k))) → ℂ,
      (∀ u, ‖r u‖ ≤ 2*(correctionMass (base.start+k))^2) →
      ∃ γ : Fin (base.size k) → ℝ, Function.Injective γ ∧
        (∀ j, γ j ∈ Set.Icc (base.height k) (base.height k+base.span k)) ∧
        (∀ T : ℝ, ((univ : Finset (Fin (base.size k))).filter
          (fun j => γ j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
        ∀ u : (coneSquare a b (quantitativeCutoff base.cutoff (base.start+k))),
          (∑ j, splineMomentCoefficient ((approachLevel d D (base.start+k):ℂ)+
            (γ j:ℂ)*Complex.I)*phase u.val (γ j))=r u

/-- Geometric finite costs and supergeometric masses give separated sparse
corrections at every stage, with geometric bounds on the same block sizes. -/
theorem exists_two_prime_sparse_spline_tail_schedule_with_geometric_sizes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D : ℝ}
    (hd : 0 < d) (hdD : d < D) :
    ∃ ss : SparsePrescribedSplineSchedule (Real.log p) (Real.log q) d D,
      ∃ U R : ℝ, 0 < U ∧ 1 < R ∧ ∀ k : ℕ, (ss.base.size k:ℝ) ≤ U*R^k := by
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
  obtain ⟨U,R,hU,hR,hfinite⟩ := exists_two_prime_sparse_spline_geometric_corrections hp hq hpq hd hdD hC
  have hδd (k : ℕ) : d ≤ approachLevel d D k := approachLevel_lower hdD k
  have hδD (k : ℕ) : approachLevel d D k ≤ D := (approachLevel_lt hdD k).le
  choose n span H₀ ε hn hspan hH₀ hε hnU hspanU hHU hεU hrealize using
    fun k => hfinite k (approachLevel d D k) (hδd k) (hδD k)
  let F := fun k : ℕ => (3+3*U)*(4*R)^k
  have hRp : 0 < R := lt_trans zero_lt_one hR
  have hF0 (k : ℕ) : 0 ≤ F k := by dsimp only [F]; positivity
  have hFbound (k : ℕ) : 3+H₀ k+span k+(gridPrefixSize n k : ℝ) ≤ F k := by
    have hpow : R^k ≤ (4*R)^k := pow_le_pow_left₀ hRp.le (by nlinarith only [hRp]) k
    have hH := (hHU k).trans (mul_le_mul_of_nonneg_left hpow hU.le)
    have hs := (hspanU k).trans (mul_le_mul_of_nonneg_left hpow hU.le)
    have hpref := gridPrefixSize_geometric_bound hU.le hR.le hnU k
    have hone : (1 : ℝ) ≤ (4*R)^k := one_le_pow₀ (by nlinarith only [hR])
    dsimp only [F]
    nlinarith only [hH,hs,hpref,hone]
  have hheight := eventually_le_matched_spline_height hn hF0 (by positivity : 0 < 4*R)
    (fun _ => le_rfl : ∀ k, F k ≤ (3+3*U)*(4*R)^k)
  have hradius := eventually_two_mass_le_radius hε hRp hεU
  have hmasslim : Tendsto (fun k : ℕ => splineNumeratorEnvelope D*(1/2 : ℝ)^k) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1)).const_mul (splineNumeratorEnvelope D)
  have hmass := hmasslim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hdouble := eventually_matched_spline_height_double hn hU hRp hnU
  obtain ⟨start,hstart⟩ := eventually_atTop.1 (hheight.and (hradius.and (hmass.and hdouble)))
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
          (hstart start le_rfl).2.2.1.le (by positivity)
        _ = _ := one_mul _
    exact ⟨hn _,hheight0,hspan _,hspH,hprefH,hmassK⟩
  have hcorrect : ∀ k,
      ∀ r : (coneSquare (Real.log p) (Real.log q) (quantitativeCutoff C (start+k))) → ℂ,
        (∀ u, ‖r u‖ ≤ 2*(correctionMass (start+k))^2) →
        ∃ γ : Fin (size k) → ℝ, Function.Injective γ ∧
          (∀ j, γ j ∈ Set.Icc (height k) (height k+span (start+k))) ∧
          (∀ T : ℝ, ((univ : Finset (Fin (size k))).filter
            (fun j => γ j ∈ Set.Icc T (T+1))).card ≤ 3) ∧
          ∀ u : (coneSquare (Real.log p) (Real.log q) (quantitativeCutoff C (start+k))),
            (∑ j, splineMomentCoefficient ((approachLevel d D (start+k):ℂ)+
              (γ j:ℂ)*Complex.I)*phase u.val (γ j))=r u := by
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

  let base : PrescribedSplineSchedule (Real.log p) (Real.log q) d D := {
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
    correct := by
      intro k r hr
      obtain ⟨γ,hinj,hmem,_,heq⟩ := hcorrect k r hr
      exact ⟨γ,hinj,hmem,heq⟩
  }
  have hgap : ∀ k, base.height k+base.span k+1 < base.height (k+1) := by
    intro k
    have htail := hstart (start+k) (by omega)
    have hdom := (hFbound (start+k)).trans htail.1
    have hnpref : (0:ℝ) ≤ gridPrefixSize n (start+k) := Nat.cast_nonneg _
    have hH0 := hH₀ (start+k)
    have hspan2 : span (start+k)+2 ≤ height k := by
      dsimp only [height,size]
      linarith only [hdom,hnpref,hH0]
    have hdbl : 2*height k ≤ height (k+1) := by
      simpa only [height,size,Nat.add_assoc] using htail.2.2.2
    change height k+span (start+k)+1 < height (k+1)
    linarith only [hspan2,hdbl]
  refine ⟨{base := base, block_gap := hgap, correct_sparse := hcorrect},
    U*R^start,R,mul_pos hU (pow_pos hRp start),hR,?_⟩
  intro k
  change (n (start+k):ℝ) ≤ (U*R^start)*R^k
  exact (hnU (start+k)).trans_eq (by rw [pow_add]; ring)

/-- The separated sparse correction schedule underlying the exact nullseries. -/
theorem exists_two_prime_sparse_spline_tail_schedule {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {d D : ℝ}
    (hd : 0 < d) (hdD : d < D) :
    Nonempty (SparsePrescribedSplineSchedule (Real.log p) (Real.log q) d D) := by
  obtain ⟨ss,_,_,_,_,_⟩ :=
    exists_two_prime_sparse_spline_tail_schedule_with_geometric_sizes hp hq hpq hd hdD
  exact ⟨ss⟩

#print axioms exists_two_prime_sparse_spline_tail_schedule_with_geometric_sizes
#print axioms exists_two_prime_sparse_spline_tail_schedule
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
