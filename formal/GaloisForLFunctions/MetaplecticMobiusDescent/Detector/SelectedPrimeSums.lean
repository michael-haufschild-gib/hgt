/-
Selected prime sums adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.HighRowsClosedForms

/-!
# Selected prime sums

Annular powers and indexed weighted slot bounds of selected prime sums; unramified marked and
selected corrections; the central-line power saving and ramified central quotients.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open ProbeLocal

def unramifiedMarked (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  markedFactor (coordR Q A x z) (coordV Q z) (Q:ℂ)⁻¹ (coordK Q eta x w)
    (-coordD Q eta v x+coordW Q v w*coordR Q A x z) 1

lemma unramifiedMarked_selected_error (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 ∧
    ‖star eta*(Q:ℂ)^x‖*‖unramifiedMarked Q A eta v x w z+coordD Q eta v x‖≤28 := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  have hR : ‖R‖≤ Q^(4-6*x.re-6*z.re) := coordR_norm_le Q hQ0 A x z hA
  have hV : ‖V‖=Q^(-6*z.re) := coordV_norm Q hQ0 z
  have hD : ‖D‖≤ Q^(-x.re) := coordD_norm_le Q hQ0 eta v x heta hv
  have hW : ‖W‖≤1 := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hK : ‖K‖≤ Q^(1-x.re-w.re) := coordK_norm_le Q hQ1 eta x w heta
  have hB : ‖B‖≤ Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by linarith))
  have hVh : ‖V‖≤1/2 := by rw [hV];exact rpow_le_half Q _ hQ (by linarith)
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hprod (a b aa bb : ℝ) (ha : 0≤ a) (hb : 0≤ b)
      (haa : a≤ Q^aa) (hbb : b≤ Q^bb) (he : aa+bb≤0) : a*b≤1 := by
    calc
      a*b≤ Q^aa*Q^bb := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _=Q^(aa+bb) := (Real.rpow_add hQ0 _ _).symm
      _≤1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 he
  have hKV : ‖K‖*‖V‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV.le (by linarith)
  have hBR : ‖B‖*‖R‖≤1 := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hB hR (by linarith)
  have hKV' : ‖K‖*‖V‖≤ Q^(1-x.re-w.re-6*z.re) := by
    calc
      _≤ Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
      _=_ := by rw [←Real.rpow_add hQ0];congr 1;ring
  have hBKV : ‖B‖*(‖K‖*‖V‖)≤1 := hprod _ _ _ _ (norm_nonneg _) (by positivity) hB hKV' (by linarith)
  have hE := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
  change ‖unramifiedMarked Q A eta v x w z+D‖≤ _ at hE
  have hE' : ‖unramifiedMarked Q A eta v x w z+D‖≤24*‖R‖+4*(‖K‖*‖V‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg R)]
  constructor
  · change ‖unramifiedMarked Q A eta v x w z+D‖≤28
    linarith
  · have hh := mul_le_mul_of_nonneg_left hE' (norm_nonneg B)
    change ‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤28
    nlinarith

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open ProbeLocal

def unramifiedSelected (Q : ℝ) (A eta v x w z : ℂ) : ℂ :=
  compensatedReplacement (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w))

lemma selected_phase_identities (Q : ℝ) (eta v x w : ℂ)
    (hQ : 0< Q) (heta : ‖eta‖=1) (hv : ‖v‖=1) :
    (star eta*(Q:ℂ)^x)*coordD Q eta v x=star v ∧
      star v*coordW Q v w=(Q:ℂ)^(-w) := by
  have hQ0 : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  constructor
  · unfold coordD
    calc
      _=(star eta*eta)*((Q:ℂ)^x*(Q:ℂ)^(-x))*star v := by ring
      _=star v := by rw [PrincipalSlotEstimate.unit_phase_inverse eta heta,←Complex.cpow_add _ _ hQ0];simp
  · unfold coordW
    rw [←mul_assoc,PrincipalSlotEstimate.unit_phase_inverse v hv,one_mul]

lemma unramifiedSelected_error_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤720 := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans (rpow_le_half Q _ hQ (by linarith))
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv.le).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have he := unramifiedMarked_selected_error Q A eta v x w z hQ hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := compensated_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v) 1
    (by norm_num) hV hW hD hq (by linarith) (by linarith)
    (by simpa using he.1) (by simpa using he.2) (by rw [norm_star,hv]) hi.1 hi.2
  simpa only [mul_one,unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

lemma unramifiedSelected_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖unramifiedSelected Q A eta v x w z‖≤961 := by
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (1/4) hQ hA heta.le hv.le
    (by norm_num) (by linarith) hz (by linarith) (by linarith)
  have hpow : Q^(-1-min (1/4:ℝ) (1/50))≤1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hH : ‖unramifiedClosed Q A eta v x w z‖≤241 := by
    have hh := norm_add_le (unramifiedClosed Q A eta v x w z-1) (1:ℂ)
    rw [sub_add_cancel,norm_one] at hh
    nlinarith
  have he := unramifiedSelected_error_bound Q A eta v x w z hQ hA heta hv hx hw hz
  have hh := norm_sub_le
    (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)
    (unramifiedClosed Q A eta v x w z*star v)
  rw [add_sub_cancel_right,norm_mul,norm_star,hv,mul_one] at hh
  linarith

lemma unramifiedSelected_zero (Q : ℝ) (v x w z : ℂ) :
    unramifiedSelected Q 0 0 v x w z= -(Q:ℂ)^(-w)*(1-coordV Q z*coordW Q v w) := by
  simp only [unramifiedSelected,unramifiedMarked,coordR,coordD,coordK,zero_mul,
    neg_zero,add_zero,markedFactor,zero_sub,sub_zero,div_one,mul_zero,
    star_zero,compensatedReplacement]
  ring

lemma unramifiedSelected_zero_bound (Q : ℝ) (v x w z : ℂ)
    (hQ : 4≤ Q) (hv : ‖v‖≤1) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖unramifiedSelected Q 0 0 v x w z‖≤2 := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hV : ‖coordV Q z‖≤1 := by
    rw [coordV_norm Q hQ0]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  have hW : ‖coordW Q v w‖≤1 :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  rw [unramifiedSelected_zero,norm_mul,norm_neg]
  have ht := norm_sub_le (1:ℂ) (coordV Q z*coordW Q v w)
  rw [norm_one,norm_mul] at ht
  have hp : ‖coordV Q z‖*‖coordW Q v w‖≤1 := by nlinarith [norm_nonneg (coordV Q z)]
  nlinarith [norm_nonneg (1-coordV Q z*coordW Q v w)]

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

lemma elementCoeff_zero_or_norm_one (eta : HeckeFamily.Character) (p : O) :
    HeckeFamily.elementCoeff eta p=0 ∨ ‖HeckeFamily.elementCoeff eta p‖=1 := by
  by_cases h : HeckeFamily.elementCoeff eta p=0
  · exact Or.inl h
  · right
    exact PrincipalSlotEstimate.actual_target_norm eta p
      (eta.residue.apply_ne_zero_iff.mp h)

def actualUnramifiedSelected (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p}) (x w z : ℂ) : ℂ :=
  unramifiedSelected (Ideal.absNorm (Ideal.span {p})) (actualAPhase eta p)
    (HeckeFamily.elementCoeff eta p)
    (complexSexticChar (Ideal.span {p}) hg (Ideal.Quotient.mk _ u)) x w z

theorem actualUnramifiedSelected_bound (eta : HeckeFamily.Character) (p u : O)
    [(Ideal.span {p}:Ideal O).IsMaximal] (hg : lambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hu : IsCoprime u p)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (x w z : ℂ)
    (hx : (7/8:ℝ)≤ x.re) (hw : (1/2:ℝ)≤ w.re) (hz : (17/50:ℝ)≤ z.re) :
    ‖actualUnramifiedSelected eta p u hg x w z‖≤961 := by
  have hv := Complex.norm_eq_one_of_pow_eq_one (ProbePhysical.complexSexticChar_unit_six p u hg hc hu) (by decide : (6:ℕ)≠0)
  unfold actualUnramifiedSelected
  rcases elementCoeff_zero_or_norm_one eta p with heta|heta
  · have hA : actualAPhase eta p=0 := by simp [actualAPhase,heta]
    rw [heta,hA]
    exact (unramifiedSelected_zero_bound _ _ x w z hQ hv.le hw hz).trans (by norm_num)
  · exact unramifiedSelected_bound _ _ _ _ x w z hQ (actualAPhase_norm_le_one eta p) heta hv hx hw hz

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeSelectedPrimeSums
local notation "O" => Eisenstein.O

lemma finite_ideal_count (S : Finset (Ideal O)) (H : ℝ) (hH : 0≤ H)
    (hS : ∀I∈S,I≠0) (hN : ∀I∈S,(Ideal.absNorm I:ℝ)≤ H) :
    (S.card:ℝ)≤128*H := by
  by_cases hh : 1≤ H
  · exact EisensteinLatticeCount.finite_ideal_count_real S H hh hS hN
  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro I hI
      have hp : (1:ℝ)≤ Ideal.absNorm I := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hS I hI))
      have := hN I hI
      linarith
    simp only [he,Finset.card_empty,Nat.cast_zero]
    positivity

lemma ramified_card_bound (eps : ℝ) (heps : 0< eps) :
    ∃C : ℝ, 0< C ∧ ∀ (U : Ideal O), U≠0 → ∀S : Finset (Ideal O),
      ((S.filter (fun P=> P∣U)).card:ℝ)≤ C*(Ideal.absNorm U:ℝ)^eps := by
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power eps heps
  refine ⟨C,hC,?_⟩
  intro U hU S
  apply (show ((S.filter (fun P=> P∣U)).card:ℝ)≤(idealDivisors U).card from ?_).trans (hb U hU)
  exact_mod_cast Finset.card_le_card (show S.filter (fun P=> P∣U)⊆idealDivisors U from by
    intro P hP
    exact (mem_idealDivisors hU).mpr (Finset.mem_filter.mp hP).2)

def annularPower (a b r : ℝ) : ℝ := max (a^r) (b^r)

lemma annularPower_nonneg (a b r : ℝ) (ha : 0< a) : 0≤ annularPower a b r :=
  (Real.rpow_nonneg ha.le _).trans (le_max_left _ _)

lemma annular_rpow (a b P q r : ℝ) (ha : 0< a) (hb : 0< b) (hP : 0< P)
    (hqa : a*P≤ q) (hqb : q≤ b*P) : q^r≤ annularPower a b r*P^r := by
  have hq : 0< q := (mul_pos ha hP).trans_le hqa
  by_cases hr : 0≤ r
  · calc
      q^r≤(b*P)^r := Real.rpow_le_rpow hq.le hqb hr
      _=b^r*P^r := Real.mul_rpow hb.le hP.le
      _≤ annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hP.le _)
  · calc
      q^r≤(a*P)^r := Real.rpow_le_rpow_of_nonpos (mul_pos ha hP) hqa (by linarith)
      _=a^r*P^r := Real.mul_rpow ha.le hP.le
      _≤ annularPower a b r*P^r := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hP.le _)

theorem annular_slot_majorant (eps a b r d : ℝ) (heps : 0< eps)
    (ha : 0< a) (hb : 0< b) (hd : d≤1) :
    ∃C : ℝ, 0< C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤ P →
    ∀S : Finset (Ideal O), (∀I∈S,I≠0) →
      (∀I∈S,a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤ b*P) →
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))
        ≤ C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨D,hD,hdiv⟩ := ramified_card_bound eps heps
  let A := annularPower a b (r-1)
  let B := annularPower a b (r-1+d)
  have hA : 0≤ A := annularPower_nonneg a b _ ha
  have hB : 0≤ B := annularPower_nonneg a b _ ha
  refine ⟨1+128*b*A+D*B,by positivity,?_⟩
  intro U hU P hP S hS hSP
  have hP0 : 0< P := by linarith
  have hU1 : (1:ℝ)≤ Ideal.absNorm U := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hUpow : 1≤(Ideal.absNorm U:ℝ)^eps := Real.one_le_rpow hU1 heps.le
  have hq (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) :=
    (mul_pos ha hP0).trans_le (hSP I hI).1
  have hc := finite_ideal_count S (b*P) (by positivity) hS (fun I hI=>(hSP I hI).2)
  have heP : P*P^(r-1)=P^r := by
    calc
      _=P^(1:ℝ)*P^(r-1) := by rw [Real.rpow_one]
      _=P^r := by rw [←Real.rpow_add hP0];congr 1;ring
  have hfirst : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))≤128*b*A*P^r := by
    calc
      _≤∑_I∈S,A*P^(r-1) := Finset.sum_le_sum (fun I hI=> annular_rpow a b P _ _ ha hb hP0 (hSP I hI).1 (hSP I hI).2)
      _=(S.card:ℝ)*(A*P^(r-1)) := by simp
      _≤(128*(b*P))*(A*P^(r-1)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=128*b*A*(P*P^(r-1)) := by ring
      _=128*b*A*P^r := by rw [heP]
  have hsecond : (∑I∈S.filter (fun I=> I∣U),(Ideal.absNorm I:ℝ)^(r-1+d))≤
      D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by
    have hpP : P^(r-1+d)≤ P^r := Real.rpow_le_rpow_of_exponent_le hP (by linarith)
    calc
      _≤∑_I∈S.filter (fun I=> I∣U),B*P^(r-1+d) := by
        apply Finset.sum_le_sum
        intro I hI
        exact annular_rpow a b P _ _ ha hb hP0 (hSP I (Finset.mem_filter.mp hI).1).1 (hSP I (Finset.mem_filter.mp hI).1).2
      _=((S.filter (fun I=> I∣U)).card:ℝ)*(B*P^(r-1+d)) := by simp
      _≤(D*(Ideal.absNorm U:ℝ)^eps)*(B*P^r) := by
        gcongr
        exact hdiv U hU S
      _=D*B*(Ideal.absNorm U:ℝ)^eps*P^r := by ring
  have hsum : (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1))≤
      (∑I∈S,(Ideal.absNorm I:ℝ)^(r-1))+
        ∑I∈S.filter (fun I=> I∣U),(Ideal.absNorm I:ℝ)^(r-1+d) := by
    rw [Finset.sum_filter,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro I hI
    split_ifs
    · rw [←Real.rpow_add (hq I hI)]
      exact le_add_of_nonneg_left (by positivity)
    · simp only [mul_one,add_zero,le_refl]
  apply hsum.trans
  have hup : 128*b*A*P^r≤128*b*A*(Ideal.absNorm U:ℝ)^eps*P^r := by
    nlinarith [mul_nonneg (show 0≤128*b*A*P^r by positivity) (show 0≤(Ideal.absNorm U:ℝ)^eps-1 by linarith)]
  nlinarith [mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤ Ideal.absNorm U) eps) (Real.rpow_nonneg hP0.le r)]

theorem weighted_slot_bound (eps a b r d B K : ℝ) (heps : 0< eps)
    (ha : 0< a) (hb : 0< b) (hd : d≤1) (hB : 0≤ B) (hK : 0≤ K) :
    ∃C : ℝ, 0< C ∧ ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤ P →
    ∀(S : Finset (Ideal O)), (∀I∈S,I≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤ B) →
    ∀(G : Ideal O→ℂ), (∀I∈S,‖G I‖≤ K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)
        ≤ C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmajor⟩ := annular_slot_majorant eps a b r d heps ha hb hd
  refine ⟨(B*K+1)*C,by positivity,?_⟩
  intro U hU P hP S hS W hWS hWB G hG z hz
  have hP0 : 0< P := by linarith
  let T := S.filter (fun I=> W ((Ideal.absNorm I:ℝ)/P)≠0)
  have hTS : T⊆S := Finset.filter_subset _ _
  have hbounds (I : Ideal O) (hI : I∈T) : a*P≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤ b*P := by
    have ht := hWS (show (Ideal.absNorm I:ℝ)/P∈Function.support W from (Finset.mem_filter.mp hI).2)
    exact ⟨(le_div_iff₀ hP0).mp ht.1,(div_le_iff₀ hP0).mp ht.2⟩
  have he : (∑I∈S,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖)=
      ∑I∈T,‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖ := by
    symm
    apply Finset.sum_subset hTS
    intro I hI hn
    have hw : W ((Ideal.absNorm I:ℝ)/P)=0 := by
      by_contra hh
      exact hn (Finset.mem_filter.mpr ⟨hI,hh⟩)
    simp only [hw,zero_mul,norm_zero]
  rw [he]
  have hpoint (I : Ideal O) (hI : I∈T) :
      ‖W ((Ideal.absNorm I:ℝ)/P)*(Ideal.absNorm I:ℂ)^(z-1)*G I‖≤
        (B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
    have hN : (0:ℝ)< Ideal.absNorm I := (mul_pos ha hP0).trans_le (hbounds I hI).1
    have hc : ‖(Ideal.absNorm I:ℂ)^(z-1)‖=(Ideal.absNorm I:ℝ)^(r-1) := by
      simpa only [Complex.ofReal_natCast,Complex.sub_re,Complex.one_re,hz] using
        Complex.norm_cpow_eq_rpow_re_of_pos hN (z-1)
    simp only [norm_mul,hc]
    calc
      _≤ B*(Ideal.absNorm I:ℝ)^(r-1)*(K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) := by
        gcongr
        · exact hWB _
        · exact hG I (hTS hI)
      _=_ := by ring
  have hmain := hmajor U hU P hP T (fun I hI=> hS I (hTS hI)) hbounds
  calc
    _≤∑I∈T,(B*K)*((Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1)) :=
      Finset.sum_le_sum hpoint
    _=(B*K)*∑I∈T,(Ideal.absNorm I:ℝ)^(r-1)*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) :=
      (Finset.mul_sum _ _ _).symm
    _≤(B*K)*(C*(Ideal.absNorm U:ℝ)^eps*P^r) := mul_le_mul_of_nonneg_left hmain (mul_nonneg hB hK)
    _≤((B*K+1)*C)*(Ideal.absNorm U:ℝ)^eps*P^r := by
      nlinarith [mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg (by positivity : (0:ℝ)≤ Ideal.absNorm U) eps))
        (Real.rpow_nonneg hP0.le r)]

end ProbeSelectedPrimeSums
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeSelectedPrimeSums
local notation "O" => Eisenstein.O

lemma weighted_slot_bound_indexed (eps a b r d B K : ℝ) (heps : 0< eps)
    (ha : 0< a) (hb : 0< b) (hd : d≤1) (hB : 0≤ B) (hK : 0≤ K) :
    ∃C : ℝ, 0< C ∧ ∀{ι : Type*} (f : ι→Ideal O), Function.Injective f →
    ∀(U : Ideal O), U≠0 → ∀P : ℝ, 1≤ P →
    ∀(S : Finset ι), (∀i∈S,f i≠0) → ∀(W : ℝ→ℂ),
      Function.support W⊆Set.Icc a b → (∀y,‖W y‖≤ B) →
    ∀(G : ι→ℂ), (∀i∈S,‖G i‖≤ K*(if f i∣U then (Ideal.absNorm (f i):ℝ)^d else 1)) →
    ∀z : ℂ, z.re=r →
      (∑i∈S,‖W ((Ideal.absNorm (f i):ℝ)/P)*(Ideal.absNorm (f i):ℂ)^(z-1)*G i‖)
        ≤ C*(Ideal.absNorm U:ℝ)^eps*P^r := by
  obtain ⟨C,hC,hmain⟩ := weighted_slot_bound eps a b r d B K heps ha hb hd hB hK
  refine ⟨C,hC,?_⟩
  intro ι f hf U hU P hP S hS W hWS hWB G hG z hz
  let G' : Ideal O→ℂ := Function.extend f G (fun _=>0)
  have he (i : ι) : G' (f i)=G i := hf.extend_apply G (fun _=>0) i
  have hI (I : Ideal O) (hI : I∈S.image f) : I≠0 := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact hS i hi
  have hg (I : Ideal O) (hI : I∈S.image f) :
      ‖G' I‖≤ K*(if I∣U then (Ideal.absNorm I:ℝ)^d else 1) := by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    rw [he]
    exact hG i hi
  have hh := hmain U hU P hP (S.image f) hI W hWS hWB G' hg z hz
  rw [Finset.sum_image hf.injOn] at hh
  simpa only [he] using hh

end ProbeSelectedPrimeSums
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => Eisenstein.O

def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=> Z^(ell j)
  let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=> canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤ C*Z^r) :
    f=O[atTop](fun Z : ℝ=> Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=> Z^(3/16+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := original_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=> h.2)⟩

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|7/8< s.re} ∧
    (∀s : ℂ,7/8< s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact ⟨excludePrimes_mask η S hS.prime,
    (sourceCorrection_differentiable η S hS).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re),
    sourceCorrection_bound η S hS⟩

end ProbeFinalAssembly
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeLocal

theorem central_phase_error_bound (V W D P B q vInv : ℂ) (A T : ℝ)
    (hA : 1≤ A) (hV : ‖V‖≤1/2) (hD : ‖D‖≤1/2)
    (hW : ‖W‖≤ A) (hq : ‖q‖≤ A) (hv : ‖vInv‖≤1)
    (hVT : A^2*‖V‖≤ T) (hDT : A^2*‖D‖≤ T)
    (hET : A^2*‖P+D‖≤28*T) (hBET : A*‖B‖*‖P+D‖≤28*T)
    (hBD : B*D=vInv) (hWq : vInv*W=q) :
    ‖compensatedReplacement V W D P B q+continuedCorrection V W D P*vInv‖≤720*T := by
  have hA0 : 0≤ A := by linarith
  have hT : 0≤ T := (mul_nonneg (sq_nonneg A) (norm_nonneg V)).trans hVT
  have h1V : ‖1-V‖≤2 := by
    have hh := norm_sub_le (1:ℂ) V
    rw [norm_one] at hh
    linarith
  have h1W : ‖1-W‖≤2*A := by
    have hh := norm_sub_le (1:ℂ) W
    rw [norm_one] at hh
    linarith
  have hdiff : ‖vInv-q‖≤2*A := (norm_sub_le vInv q).trans (by linarith)
  have hfac : ‖(1-V)*(1-W)/(1-D)‖≤8*A := by
    rw [div_eq_mul_inv,norm_mul,norm_mul]
    have hi := inv_one_sub_norm_le_two D hD
    calc
      _ ≤ 2*(2*A)*2 := by gcongr
      _ = _ := by ring
  have hleft : ‖(vInv-q)*(V/(1-V)-D)‖≤2*A*(2*‖V‖+‖D‖) := by
    rw [norm_mul]
    apply mul_le_mul hdiff _ (norm_nonneg _) (by positivity)
    calc
      _ ≤ ‖V/(1-V)‖+‖D‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [div_eq_mul_inv,norm_mul]
        have hi := inv_one_sub_norm_le_two V hV
        nlinarith [mul_le_mul_of_nonneg_left hi (norm_nonneg V)]
  have hright : ‖(B+vInv-q)*(P+D)‖≤(‖B‖+2*A)*‖P+D‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ = ‖B+(vInv-q)‖ := by congr 1;ring
      _ ≤ ‖B‖+‖vInv-q‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  rw [continued_normalized_cancellation V W D P B q vInv
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD) hBD hWq,norm_mul]
  calc
    _ ≤ (8*A)*(2*A*(2*‖V‖+‖D‖)+(‖B‖+2*A)*‖P+D‖) := by
      apply mul_le_mul hfac _ (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add hleft hright)
    _ = 32*(A^2*‖V‖)+16*(A^2*‖D‖)+8*(A*‖B‖*‖P+D‖)+16*(A^2*‖P+D‖) := by ring
    _ ≤ 720*T := by linarith

end ProbeLocal
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open ProbeLocal

lemma central_unramified_error_weights (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤ Q) (ha : (51/100:ℝ)≤ a) (ha1 : a≤1) (he : 0< e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    let L := Q^(6*e)
    let E := unramifiedMarked Q A eta v x w z+coordD Q eta v x
    L^2*‖coordV Q z‖≤ Q^(-(51/100:ℝ)) ∧
    L^2*‖coordD Q eta v x‖≤ Q^(-(51/100:ℝ)) ∧
    L^2*‖E‖≤28*Q^(-(51/100:ℝ)) ∧
    L*‖star eta*(Q:ℂ)^x‖*‖E‖≤28*Q^(-(51/100:ℝ)) := by
  dsimp only
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  let R := coordR Q A x z
  let V := coordV Q z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  let B := star eta*(Q:ℂ)^x
  let L : ℝ := Q^(6*e)
  have hL : 1≤ L := Real.one_le_rpow hQ1 (by positivity)
  have hL0 : 0≤ L := by positivity
  have hR := coordR_norm_le Q hQ0 A x z hA
  have hV := coordV_norm Q hQ0 z
  have hD := coordD_norm_le Q hQ0 eta v x heta hv
  have hK := coordK_norm_le Q hQ1 eta x w heta
  have hW : ‖W‖≤ L := (coordW_norm_le Q hQ0 v w hv).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hB : ‖B‖≤ Q^x.re := by
    dsimp only [B]
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hRh : ‖R‖≤1/2 := hR.trans (rpow_le_half Q _ hQ (by rw [hx,hz];linarith))
  have hVh : ‖V‖≤1/2 := hV.le.trans (rpow_le_half Q _ hQ (by rw [hz];norm_num))
  have hDh : ‖D‖≤1/2 := hD.trans (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hqi : ‖(Q:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hQ0,←one_div]
    exact (div_le_one hQ0).mpr hQ1
  have hE : ‖unramifiedMarked Q A eta v x w z+D‖≤24*L*‖R‖+4*‖K‖*‖V‖ := by
    have hh := unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left (show 1+‖W‖≤2*L by linarith) (norm_nonneg R)]
  have weighted (k r : ℝ) (N : ℝ) (hN : N≤ Q^r) (hexp : k+r≤-(51/100:ℝ)) :
      Q^k*N≤ Q^(-(51/100:ℝ)) := by
    calc
      _ ≤ Q^k*Q^r := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg hQ0.le _)
      _ = Q^(k+r) := (Real.rpow_add hQ0 _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hQ1 hexp
  have hLR : L^3*‖R‖≤ Q^(-(51/100:ℝ)) := by
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hR (by rw [hx,hz];linarith)
  have hLKV : L^2*(‖K‖*‖V‖)≤ Q^(-(51/100:ℝ)) := by
    have hkv : ‖K‖*‖V‖≤ Q^(1-x.re-w.re-6*z.re) := by
      calc
        _ ≤ Q^(1-x.re-w.re)*Q^(-6*z.re) := mul_le_mul hK hV.le (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hkv (by rw [hx,hw,hz];linarith)
  have hLBR : L^2*(‖B‖*‖R‖)≤ Q^(-(51/100:ℝ)) := by
    have hbr : ‖B‖*‖R‖≤ Q^(4-5*x.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(4-6*x.re-6*z.re) := mul_le_mul hB hR (norm_nonneg _) (Real.rpow_nonneg hQ0.le _)
        _ = _ := by rw [←Real.rpow_add hQ0];congr 1;ring
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hbr (by rw [hx,hz];linarith)
  have hLBKV : L*(‖B‖*‖K‖*‖V‖)≤ Q^(-(51/100:ℝ)) := by
    have hbkv : ‖B‖*‖K‖*‖V‖≤ Q^(1-w.re-6*z.re) := by
      calc
        _ ≤ Q^x.re*Q^(1-x.re-w.re)*Q^(-6*z.re) := by
          gcongr
          exact hV.le
        _ = _ := by rw [←Real.rpow_add hQ0,←Real.rpow_add hQ0];congr 1;ring
    exact weighted _ _ _ hbkv (by rw [hw,hz];linarith)
  refine ⟨?_,?_,?_,?_⟩
  · change L^2*‖V‖≤ _
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hV.le (by rw [hz];linarith)
  · change L^2*‖D‖≤ _
    dsimp [L]
    rw [←Real.rpow_mul_natCast hQ0.le]
    exact weighted _ _ _ hD (by rw [hx];linarith)
  · have hh := mul_le_mul_of_nonneg_left hE (sq_nonneg L)
    change L^2*‖unramifiedMarked Q A eta v x w z+D‖≤ _
    nlinarith [hLR,hLKV]
  · have hh := mul_le_mul_of_nonneg_left hE (mul_nonneg hL0 (norm_nonneg B))
    change L*‖B‖*‖unramifiedMarked Q A eta v x w z+D‖≤ _
    nlinarith [hLBR,hLBKV]

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open ProbeLocal

lemma unramifiedSelected_central_error (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 4≤ Q) (ha : (51/100:ℝ)≤ a) (ha1 : a≤1) (he : 0< e) (he1 : e≤1/1000)
    (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v‖≤
      720*Q^(-(51/100:ℝ)) := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hL : 1≤ Q^(6*e) := Real.one_le_rpow hQ1 (by positivity)
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by rw [hz];norm_num)
  have hD : ‖coordD Q eta v x‖≤1/2 :=
    (coordD_norm_le Q hQ0 eta v x heta.le hv.le).trans
      (rpow_le_half Q _ hQ (by rw [hx];linarith))
  have hW : ‖coordW Q v w‖≤ Q^(6*e) := (coordW_norm_le Q hQ0 v w hv.le).trans
    (Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith))
  have hq : ‖(Q:ℂ)^(-w)‖≤ Q^(6*e) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  obtain ⟨hVT,hDT,hET,hBET⟩ := central_unramified_error_weights Q a e A eta v x w z
    hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hi := selected_phase_identities Q eta v x w hQ0 heta hv
  have hh := central_phase_error_bound (coordV Q z) (coordW Q v w) (coordD Q eta v x)
    (unramifiedMarked Q A eta v x w z) (star eta*(Q:ℂ)^x) ((Q:ℂ)^(-w)) (star v)
    (Q^(6*e)) (Q^(-(51/100:ℝ))) hL hV hD hW hq (by rw [norm_star,hv])
    hVT hDT hET hBET hi.1 hi.2
  simpa only [unramifiedSelected,unramifiedClosed,unramifiedMarked] using hh

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler

lemma unramifiedClosed_central_lower (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤ Q) (ha : (51/100:ℝ)≤ a) (ha1 : a≤1)
    (he : 0< e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖unramifiedClosed Q A eta v x w z‖ := by
  have hQ0 : 0< Q := by linarith
  have hd := unramifiedClosed_first_region_bound Q A eta v x w z (10*e)
    (by linarith) hA heta hv (by positivity) (by rw [hx];linarith)
    (by rw [hz]) (by rw [hw];linarith) (by rw [hx,hw];linarith)
  have hp : Q^(-1-min (10*e) (1/50:ℝ))≤ Q^(-1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by
      have hm : 0≤ min (10*e) (1/50:ℝ) := by positivity
      linarith)
  have hi : Q^(-1:ℝ)≤1/480 := by
    rw [Real.rpow_neg_one,←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hQ
  have ht := norm_sub_le (1:ℂ) (unramifiedClosed Q A eta v x w z)
  have ht' := norm_add_le (1-unramifiedClosed Q A eta v x w z)
    (unramifiedClosed Q A eta v x w z)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at ht'
  nlinarith

lemma unramifiedSelected_central_quotient (Q a e : ℝ) (A eta v x w z : ℂ)
    (hQ : 480≤ Q) (ha : (51/100:ℝ)≤ a) (ha1 : a≤1)
    (he : 0< e) (he1 : e≤1/1000) (hA : ‖A‖≤1) (heta : ‖eta‖=1) (hv : ‖v‖=1)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v‖≤
      1440*Q^(-(51/100:ℝ)) := by
  have hh := unramifiedClosed_central_lower Q a e A eta v x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  have hn : unramifiedClosed Q A eta v x w z≠0 := by
    intro hz;rw [hz,norm_zero] at hh;norm_num at hh
  have hp : 0<‖unramifiedClosed Q A eta v x w z‖ := by linarith
  have hb := unramifiedSelected_central_error Q a e A eta v x w z
    (by linarith) ha ha1 he he1 hA heta hv hx hw hz
  have hid : unramifiedSelected Q A eta v x w z/unramifiedClosed Q A eta v x w z+star v=
      (unramifiedSelected Q A eta v x w z+unramifiedClosed Q A eta v x w z*star v)/
      unramifiedClosed Q A eta v x w z := by field_simp
  rw [hid,norm_div]
  apply (div_le_iff₀ hp).mpr
  have ht : 0≤ Q^(-(51/100:ℝ)) := Real.rpow_nonneg (by linarith) _
  nlinarith
end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

/-- The nonexceptional base exponents give the central-line power saving. -/
private lemma sourceBase_central_exponent (alpha eps : ℝ)
    (halpha : (51/100:ℝ)≤alpha) (halpha1 : alpha≤1)
    (heps : 0<eps) (heps1 : eps≤1/1000)
    (e l k m : ℕ) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
    sourceBaseExponent e l k m-(alpha+16*eps+1/2)*(e:ℝ)-
      (1+3*(alpha+16*eps))*(l:ℝ)-(1-alpha-6*eps)*(k:ℝ)-
      6*(17/50:ℝ)*(m:ℝ)≤1/2-(alpha+16*eps) := by
  have hzm : 0≤6*(17/50:ℝ)*(m:ℝ) := by positivity
  have hzm1 (hm : m≠0) : 6*(17/50:ℝ)≤6*(17/50:ℝ)*(m:ℝ) := by
    have hm1 : (1:ℝ)≤ m := by exact_mod_cast (by omega : 1≤ m)
    linarith only [hm1]
  rcases hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  all_goals rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hk with rfl|rfl
  all_goals by_cases hm : m=0
  all_goals norm_num [hm] at hstrict
  all_goals norm_num [sourceBaseExponent,hm]
  all_goals first
    | linarith only [halpha,halpha1,heps,heps1,hzm]
    | linarith only [halpha,halpha1,heps,heps1,hzm,hzm1 hm]

include hc in
theorem sourceRowTerm_central_nonstrict (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l k m : ℕ) (hj : j<6) (hk : k≤1)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1))
    (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
    ‖sourceRowTerm p hp hg eta a rho x w z j e l k m‖≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2-x.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j e l k m (sourceBaseExponent e l k m) (1/2-x.re)
  · exact sourceBase_scalar_bound p hp hg hc j e l k m hj hk hf
  · rw [hx,hw,hz]
    exact sourceBase_central_exponent alpha eps halpha halpha1 heps heps1
      e l k m hk hf hstrict

end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma rowBaseFinite_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j e l : ℕ) (hj : j<6)
    (hf : (e=0 ∧ l=2) ∨ (e=1 ∧ l=0) ∨ (e=0 ∧ l=1) ∨ (e=1 ∧ l=1)) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let T := fun k m=> rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
    ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-
      (if e=1 ∧ l=0 then T 1 0 else 0)‖≤16*Q^(1/2-x.re) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  let T := fun k m=> rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l k m
  have hpow : 0≤ Q^(1/2-x.re) := by positivity
  have hv := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_V_half _ hQ z (by rw [hz]))
  have ht (k m : ℕ) (hk : k≤1) (hstrict : ¬(e=1 ∧ l=0 ∧ k=1 ∧ m=0)) :
      ‖T k m‖≤2*Q^(1/2-x.re) := by
    have ht0 : e+3*l≠0 := by rcases hf with h|h|h|h <;> omega
    dsimp only [T,Q]
    simp only [Complex.ofReal_natCast]
    rw [←sourceRowTerm_pos p hp hg eta a rho x w z j e l k m ht0]
    exact sourceRowTerm_central_nonstrict p hp hg hc eta a rho x w z alpha eps
      heta ha hρ halpha halpha1 heps heps1 hx hw hz j e l k m hj hk hf hstrict
  have hd (k : ℕ) (hk : k≤1) : ‖T k 2/(1-coordV Q z)‖≤4*Q^(1/2-x.re) := by
    rw [div_eq_mul_inv,norm_mul]
    exact (mul_le_mul (ht k 2 hk (by omega)) hv (norm_nonneg _) (by positivity)).trans_eq (by ring)
  by_cases hb : e=1 ∧ l=0
  · rw [if_pos hb]
    have hid : rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0=
        ((T 0 0+T 0 1+T 0 2/(1-coordV Q z))+T 1 1)+T 1 2/(1-coordV Q z) := by
      simp only [rowBaseFinite,Fin.sum_univ_two]
      dsimp only [T]
      norm_num only [Fin.val_zero,Fin.val_one]
      ring
    change ‖rowBaseFinite p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j e l-T 1 0‖≤ _
    rw [hid]
    have h00 := ht 0 0 (by omega) (by omega)
    have h01 := ht 0 1 (by omega) (by omega)
    have h11 := ht 1 1 (by omega) (by omega)
    have hn := (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h00 h01)) (hd 0 (by omega)))) h11)) (hd 1 (by omega)))
    exact hn.trans (by linarith)
  · rw [if_neg hb,sub_zero]
    unfold rowBaseFinite
    apply (norm_sum_le _ _).trans
    calc
      _≤∑ _k : Fin 2,8*Q^(1/2-x.re) := by
        apply Finset.sum_le_sum
        intro k hk
        have h0 := ht k.val 0 (by omega) (by tauto)
        have h1 := ht k.val 1 (by omega) (by omega)
        exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h0 h1)) (hd k.val (by omega)))).trans_eq (by ring)
      _=16*Q^(1/2-x.re) := by simp;ring

include hc in
theorem rowClosedMarked_central_remainder (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    let R := evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z)
    let T := rowMarkedTerm p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0
    ‖rowClosedMarked p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) rho j-T/(1-R)‖≤
      128*Q^(1/2-x.re) := by
  dsimp only
  have h02 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 2 hj (by omega)
  have h10 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 0 hj (by omega)
  have h01 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 0 1 hj (by omega)
  have h11 := rowBaseFinite_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ halpha halpha1 heps heps1 hx hw hz j 1 1 hj (by omega)
  dsimp only at h02 h10 h01 h11
  norm_num only [and_true,true_and,and_false,false_and,Nat.reduceEqDiff,ite_true,ite_false,sub_zero] at h02 h10 h01 h11
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  simp only [Complex.ofReal_natCast] at *
  unfold rowClosedMarked
  rw [←sub_div,div_eq_mul_inv,norm_mul]
  have heq (A B C D T : ℂ) : A+B+C+D-T=A+(B-T)+C+D := by ring
  rw [heq]
  apply (mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h02 h10)) h01)) h11)) (norm_nonneg _)).trans
  calc
    _≤(16*(_ : ℝ)+16*_+16*_+16*_)*2 := mul_le_mul_of_nonneg_left hr (by positivity)
    _=_ := by ring
end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePrimePower
open Eisenstein CompletedGauss 
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma squarefree_base_boundary_norm (j : ℕ) (hj : j≤1) :
    ‖positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 0 1 j‖≤
      Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j (by omega)
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  rw [he,if_neg (by omega)]
  split_ifs
  · rw [norm_mul,norm_mul,norm_inv,
      Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_neg_one_sq _ hg) (by decide),
      inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
    norm_num
  · simp only [mul_zero,norm_zero]
    positivity

include hc in
lemma squarefree_base_strict_norm (j : ℕ) (hj : j<6) :
    ‖positiveScalar p hp.ne_zero (complexSexticChar (Ideal.span {p}) hg) 0 1 j‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
  have he := row_squarefree_kone p hp hg hc 0 0 j hj
  norm_num only [Nat.mul_zero,zero_add,mul_zero,add_zero,pow_zero,one_mul] at he
  have hQ : (0:ℝ)< Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hQ1 : (1:ℝ)≤ Ideal.absNorm (Ideal.span {p}) := by
    have hh := HeckeIdealSeries.prime_norm_two_le
      ⟨Ideal.span {p},Ideal.prime_span_singleton_iff.mpr hp⟩
    change 2≤ Ideal.absNorm (Ideal.span {p}) at hh
    exact_mod_cast (show 1≤ Ideal.absNorm (Ideal.span {p}) by omega)
  have hfac : ‖if 1< j then (Ideal.absNorm (Ideal.span {p}):ℂ)-1 else if j=1 ∧ True then -(1:ℂ) else 0‖≤
      (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    split_ifs
    · rw [←Complex.ofReal_natCast,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
        Real.norm_eq_abs,abs_of_nonneg (by linarith)]
      linarith
    · simpa using hQ1
    · simp
  rw [he,norm_mul,norm_mul,norm_inv,
    Complex.norm_eq_one_of_pow_eq_one (complexSexticChar_neg_one_sq _ hg) (by decide),
    inv_one,one_mul,primeGauss_actual_norm p hp.ne_zero hg hc]
  calc
    _≤ Real.sqrt (Ideal.absNorm (Ideal.span {p}):ℝ)*(Ideal.absNorm (Ideal.span {p}):ℝ) :=
      mul_le_mul_of_nonneg_left hfac (Real.sqrt_nonneg _)
    _=(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by
      rw [mul_comm]
      convert ProbeEuler.pow_mul_sqrt (Ideal.absNorm (Ideal.span {p}):ℝ) hQ 1 using 1 <;> norm_num
end ProbePrimePower
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

include hc in
lemma sourceRowTerm_central_strict_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j<6) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (3/2) (1-x.re-w.re)
  · have hb := squarefree_base_strict_norm p hp hg hc j hj
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(3/2:ℝ) by linarith)
  · norm_num ; linarith

include hc in
lemma sourceRowTerm_central_boundary_norm (eta a rho x w z : ℂ)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1) (j : ℕ) (hj : j≤1) :
    ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-x.re-w.re) := by
  apply sourceRowTerm_norm_from_scalar_power p hp hg hc eta a rho x w z heta ha hρ
    j 1 0 1 0 (1/2) (-x.re-w.re)
  · have hb := squarefree_base_boundary_norm p hp hg hc j hj
    rw [Real.sqrt_eq_rpow] at hb
    have ht : 0≤(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by positivity
    simpa only [sourceScalar,Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub,ite_false,
      Nat.reduceEqDiff,mul_zero,add_zero] using hb.trans (show _≤2*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) by linarith)
  · norm_num
end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

def ramifiedStrictSelected (eta a rho x w z : ℂ) (j : ℕ) : ℂ :=
  star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x*(1-coordV (Ideal.absNorm (Ideal.span {p})) z)*
    (rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
        (coordV (Ideal.absNorm (Ideal.span {p})) z)))

include hc in
theorem ramifiedSelected_central_regular (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedSelected p hp hg eta a rho x w z j-ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      385*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1/2:ℝ) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0< Q := by dsimp [Q];linarith
  have hQ1 : 1≤ Q := by linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have hH := ramifiedClosed_first_region_bound p hp hg hc eta a rho x w z hQ heta ha hρ
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith) j hj
  have hV := first_region_V_half _ hQ z (by rw [hz])
  have h1V : ‖1-coordV Q z‖≤3/2 := by
    have h := norm_sub_le (1:ℂ) (coordV Q z)
    rw [norm_one] at h
    change ‖coordV Q z‖≤1/2 at hV
    linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤ Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  have hqw : ‖(Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)‖≤ Q^(1/2:ℝ) := by
    rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
  have hid (B V M T q H : ℂ) : B*V*M-q*H-B*V*T=B*V*(M-T)-q*H := by ring
  unfold ramifiedSelected ramifiedStrictSelected
  rw [hid]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*(128*Q^(1/2-x.re))+Q^(1/2:ℝ)*193 := by
      gcongr
    _=385*Q^(1/2:ℝ) := by
      have ht : Q^x.re*Q^(1/2-x.re)=Q^(1/2:ℝ) := by rw [←Real.rpow_add hQ0];congr 1;ring
      nlinarith [ht]
end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)

lemma ramifiedStrictSelected_from_entry (eta a rho x w z : ℂ) (j : ℕ) (b : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p})) (heta : ‖eta‖≤1) (ha : ‖a‖≤1)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re)
    (ht : ‖sourceRowTerm p hp hg eta a rho x w z j 1 0 1 0‖≤
      2*(Ideal.absNorm (Ideal.span {p}):ℝ)^b) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(x.re+b) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0< Q := by dsimp [Q];linarith
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha hx hz)
  simp only [Complex.ofReal_natCast] at hr
  have hv := first_region_V_half _ hQ z hz
  have hs := norm_sub_le (1:ℂ) (coordV Q z)
  rw [norm_one] at hs
  have h1V : ‖1-coordV Q z‖≤3/2 := by change ‖coordV Q z‖≤1/2 at hv;linarith
  have hphase : ‖star eta*(Ideal.absNorm (Ideal.span {p}):ℂ)^x‖≤ Q^x.re := by
    rw [norm_mul,norm_star,←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) heta
  unfold ramifiedStrictSelected
  rw [div_eq_mul_inv]
  simp only [norm_mul] at hphase ⊢
  calc
    _≤(Q^x.re*(3/2))*((2*Q^b)*2) := by gcongr
    _=6*Q^(x.re+b) := by rw [Real.rpow_add hQ0];ring

include hc in
theorem ramifiedStrictSelected_central_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) (j : ℕ) (hj : j<6) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(1-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (1-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring

include hc in
theorem ramifiedStrictSelected_boundary_norm (eta a rho x w z : ℂ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (hx : (51/100:ℝ)≤ x.re) (hz : (17/50:ℝ)≤ z.re) (j : ℕ) (hj : j≤1) :
    ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖≤
      6*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-w.re) := by
  have hb := ramifiedStrictSelected_from_entry p hp hg eta a rho x w z j (-x.re-w.re)
    hQ heta ha hx hz (sourceRowTerm_central_boundary_norm p hp hg hc eta a rho x w z heta ha hρ j hj)
  convert hb using 1 ; congr 2 ; ring
end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O
variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
lemma rowClosedMarked_central_size (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖rowClosedMarked p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z) rho j‖≤
      132*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ1 : 1≤ Q := by dsimp [Q];linarith
  have hrem := rowClosedMarked_central_remainder p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  dsimp only at hrem
  simp only [Complex.ofReal_natCast] at hrem
  have ht := sourceRowTerm_central_strict_norm p hp hg hc eta a rho x w z heta ha hρ j hj
  rw [sourceRowTerm_pos p hp hg eta a rho x w z j 1 0 1 0 (by omega)] at ht
  have hr := ProbeLocal.inv_one_sub_norm_le_two _ (first_region_R_half _ hQ a x z ha (by rw [hx];linarith) (by rw [hz]))
  have he : Q^(1-x.re-w.re)=Q^(-10*eps) := by congr 1;rw [hx,hw];ring
  have hn : Q^(1/2-x.re)≤ Q^(-10*eps) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hx];linarith)
  have hdiv : ‖rowMarkedTerm p hp hg eta a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV Q z) rho j 1 0 1 0 /
      (1-evenRatio (Ideal.absNorm (Ideal.span {p})) a ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV Q z))‖≤4*Q^(-10*eps) := by
    rw [div_eq_mul_inv,norm_mul]
    have hh := mul_le_mul ht hr (norm_nonneg _) (by positivity)
    exact hh.trans_eq (by change (2*Q^(1-x.re-w.re))*2=4*Q^(-10*eps);rw [he];ring)
  dsimp only [Q] at hdiv
  have hh := (norm_add_le _ _).trans (add_le_add hrem hdiv)
  simp only [sub_add_cancel] at hh
  exact hh.trans (by change 128*Q^(1/2-x.re)+4*Q^(-10*eps)≤132*Q^(-10*eps);nlinarith)

include hc in
theorem ramifiedClosed_central_defect (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    ‖ramifiedClosed p hp hg eta a rho x w z j-1‖≤
      198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps) := by
  have hb := rowClosedMarked_central_size p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hv := first_region_V_half _ hQ z (by rw [hz])
  have hs := norm_sub_le (1:ℂ) (coordV (Ideal.absNorm (Ideal.span {p})) z)
  rw [norm_one] at hs
  unfold ramifiedClosed
  rw [add_sub_cancel_left,norm_mul]
  apply (mul_le_mul (show ‖1-coordV (Ideal.absNorm (Ideal.span {p})) z‖≤3/2 by linarith)
    hb (norm_nonneg _) (by norm_num : (0:ℝ)≤3/2)).trans_eq
  ring
end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Topology
open Filter
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

theorem central_correction_threshold (eps : ℝ) (heps : 0< eps) :
    ∃Q0 : ℝ,480≤ Q0 ∧ ∀Q : ℝ,Q0≤ Q→198*Q^(-10*eps)≤1/2 := by
  have hh : Tendsto (fun Q : ℝ=>198*Q^(-10*eps)) atTop (nhds 0) := by
    simpa only [mul_zero,neg_mul] using
      (tendsto_rpow_neg_atTop (show 0<10*eps by positivity)).const_mul (198:ℝ)
  have he := hh.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))
  obtain ⟨Q0,hQ0⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 480 Q0,le_max_left _ _,?_⟩
  intro Q hQ
  exact (hQ0 Q ((le_max_right _ _).trans hQ)).le

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedClosed_central_lower (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    1/2≤‖ramifiedClosed p hp hg eta a rho x w z j‖ := by
  have hd := ramifiedClosed_central_defect p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hh := norm_add_le (1-ramifiedClosed p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j)
  rw [sub_add_cancel,norm_one,norm_sub_rev] at hh
  linarith
end ProbeEuler
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeEuler
open Eisenstein CompletedGauss  ProbePrimePower
local notation "O" => Eisenstein.O

lemma norm_div_le_twice (A H : ℂ) (hH : 1/2≤‖H‖) : ‖A/H‖≤2*‖A‖ := by
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0<‖H‖)).mpr
  nlinarith [norm_nonneg A]

variable (p : O) (hp : Prime p) [(Ideal.span {p}:Ideal O).IsMaximal]
  (hg : lambda∉Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
include hc in
theorem ramifiedSelected_central_quotient (eta a rho x w z : ℂ) (alpha eps : ℝ)
    (hQ : (4:ℝ)≤ Ideal.absNorm (Ideal.span {p}))
    (hsmall : 198*(Ideal.absNorm (Ideal.span {p}):ℝ)^(-10*eps)≤1/2)
    (heta : ‖eta‖≤1) (ha : ‖a‖≤1) (hρ : rho^6=1)
    (halpha : (51/100:ℝ)≤ alpha) (halpha1 : alpha≤1) (heps : 0< eps) (heps1 : eps≤1/1000)
    (hx : x.re=alpha+16*eps) (hw : w.re=1-alpha-6*eps) (hz : z.re=17/50)
    (j : ℕ) (hj : j<6) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    Q^(-1:ℝ)*‖ramifiedSelected p hp hg eta a rho x w z j /
      ramifiedClosed p hp hg eta a rho x w z j‖≤
      800*Q^(-(1/2:ℝ))+(if 2≤ j then 12*Q^(-w.re) else 0) := by
  dsimp only
  let Q : ℝ := Ideal.absNorm (Ideal.span {p})
  have hQ0 : 0< Q := by dsimp [Q];linarith
  have hQ1 : 1≤ Q := by linarith
  have hH := ramifiedClosed_central_lower p hp hg hc eta a rho x w z alpha eps hQ hsmall heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hreg := ramifiedSelected_central_regular p hp hg hc eta a rho x w z alpha eps hQ heta ha hρ
    halpha halpha1 heps heps1 hx hw hz j hj
  have hnorm := norm_div_le_twice (ramifiedSelected p hp hg eta a rho x w z j)
    (ramifiedClosed p hp hg eta a rho x w z j) hH
  have htri := (norm_add_le _ _).trans (add_le_add hreg (le_refl ‖ramifiedStrictSelected p hp hg eta a rho x w z j‖))
  rw [sub_add_cancel] at htri
  have hpow : Q^(-1:ℝ)*Q^(1/2:ℝ)=Q^(-(1/2:ℝ)) := by rw [←Real.rpow_add hQ0];norm_num
  have hqi : 0≤ Q^(-1:ℝ) := Real.rpow_nonneg hQ0.le _
  by_cases hj2 : 2≤ j
  · rw [if_pos hj2]
    have hs := ramifiedStrictSelected_central_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j hj
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤385*Q^(1/2:ℝ)+6*Q^(1-w.re) := by linarith
    have hprod : Q^(-1:ℝ)*Q^(1-w.re)=Q^(-w.re) := by rw [←Real.rpow_add hQ0];congr 1;ring
    calc
      _≤ Q^(-1:ℝ)*(2*(385*Q^(1/2:ℝ)+6*Q^(1-w.re))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=770*Q^(-(1/2:ℝ))+12*Q^(-w.re) := by nlinarith [hpow,hprod]
      _≤ _ := by nlinarith [Real.rpow_nonneg hQ0.le (-(1/2:ℝ))]
  · rw [if_neg hj2,add_zero]
    have hs := ramifiedStrictSelected_boundary_norm p hp hg hc eta a rho x w z hQ heta ha hρ
      (by rw [hx];linarith) (by rw [hz]) j (by omega)
    have hqw : Q^(-w.re)≤ Q^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by rw [hw];linarith)
    have hb : ‖ramifiedSelected p hp hg eta a rho x w z j‖≤391*Q^(1/2:ℝ) := by nlinarith
    calc
      _≤ Q^(-1:ℝ)*(2*(391*Q^(1/2:ℝ))) := mul_le_mul_of_nonneg_left (hnorm.trans (by linarith)) hqi
      _=782*Q^(-(1/2:ℝ)) := by nlinarith [hpow]
      _≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _)
end ProbeEuler
end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
