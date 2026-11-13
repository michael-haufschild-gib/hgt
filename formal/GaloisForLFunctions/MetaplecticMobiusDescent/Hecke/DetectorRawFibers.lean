/-
Raw fibers of the detector adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SecondChildPowerBudgets
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.DetectorWitnessRows

/-!
# Raw fibers of the detector

Raw fibers fixing witness labels, dyadic scales and prime-amplitude bins; batches, physical
selections and weighted means; fixed-amplitude and high-batch counts from raw moments.
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
open scoped Classical BigOperators
open Set
namespace HeckePrimeAmplitudeBins

def amplitude (P cap mesh : ℝ) (Q : ℂ) : ℝ :=
  if Q=0 then 0 else min cap (max 0 (mesh*(⌊Real.log ‖Q‖/(mesh*Real.log P)⌋ : ℤ)))

theorem amplitude_bounds (P cap mesh : ℝ) (Q : ℂ) (hcap : 0≤ cap) :
    0≤ amplitude P cap mesh Q ∧ amplitude P cap mesh Q≤ cap := by
  unfold amplitude
  split_ifs
  · exact ⟨le_rfl,hcap⟩
  · exact ⟨le_min hcap (le_max_left _ _),min_le_left _ _⟩

theorem amplitude_upper (P cap mesh : ℝ) (Q : ℂ) (hP : 1< P) (hm : 0< mesh)
    (hbound : ‖Q‖≤ P^(cap+mesh)) :
    ‖Q‖≤ P^(amplitude P cap mesh Q+mesh) := by
  by_cases hQ : Q=0
  · subst Q
    simp only [norm_zero,amplitude,ite_true,zero_add]
    exact Real.rpow_nonneg (by linarith) _
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0< Real.log P := Real.log_pos hP
  have hd : 0< mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  by_cases hc : cap≤ max 0 (mesh*(n : ℝ))
  · simpa [amplitude,hQ,n,min_eq_left hc] using hbound
  · have he : amplitude P cap mesh Q=max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,if_neg hQ]
      exact min_eq_right (le_of_not_ge hc)
    rw [he]
    apply (Real.le_rpow_iff_log_le hx (by linarith : 0< P)).mpr
    have hn : Real.log ‖Q‖/(mesh*Real.log P)<(n : ℝ)+1 := Int.lt_floor_add_one _
    have hn' := (div_lt_iff₀ hd).mp hn
    have hg := mul_le_mul_of_nonneg_right (le_max_right 0 (mesh*(n : ℝ))) hl.le
    nlinarith

theorem amplitude_lower (P cap mesh : ℝ) (Q : ℂ) (hP : 1< P) (hm : 0< mesh)
    (hg : 0< amplitude P cap mesh Q) :
    P^(amplitude P cap mesh Q)≤‖Q‖ := by
  have hQ : Q≠0 := by intro h; simp [amplitude,h] at hg
  have hx : 0<‖Q‖ := norm_pos_iff.mpr hQ
  have hl : 0< Real.log P := Real.log_pos hP
  have hd : 0< mesh*Real.log P := mul_pos hm hl
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have hpos : 0< mesh*(n : ℝ) := by
    have hmin : amplitude P cap mesh Q≤ max 0 (mesh*(n : ℝ)) := by
      simp only [amplitude,if_neg hQ]
      exact min_le_right _ _
    have ht : 0< max 0 (mesh*(n : ℝ)) := hg.trans_le hmin
    exact (lt_max_iff.mp ht).resolve_left (lt_irrefl _)
  have he : amplitude P cap mesh Q=min cap (mesh*(n : ℝ)) := by
    simp only [amplitude,if_neg hQ]
    rw [max_eq_right hpos.le]
  have hn : (n : ℝ)≤ Real.log ‖Q‖/(mesh*Real.log P) := Int.floor_le _
  have hn' := (le_div_iff₀ hd).mp hn
  have hb : amplitude P cap mesh Q*Real.log P≤ Real.log ‖Q‖ := by
    rw [he]
    have hh := mul_le_mul_of_nonneg_right (min_le_right cap (mesh*(n : ℝ))) hl.le
    nlinarith
  have hpow : 0< P^(amplitude P cap mesh Q) := Real.rpow_pos_of_pos (by linarith) _
  apply (Real.log_le_log_iff hpow hx).mp
  rw [Real.log_rpow (by linarith : 0< P)]
  exact hb

def labels (cap mesh : ℝ) : Finset ℝ :=
  insert 0 (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))

theorem amplitude_mem_labels (P cap mesh : ℝ) (Q : ℂ) (hm : 0< mesh) :
    amplitude P cap mesh Q∈labels cap mesh := by
  by_cases hQ : Q=0
  · simp [amplitude,hQ,labels]
  let n : ℤ := ⌊Real.log ‖Q‖/(mesh*Real.log P)⌋
  have he : amplitude P cap mesh Q=min cap (max 0 (mesh*(n : ℝ))) := by
    simp only [amplitude,if_neg hQ]
    rfl
  rw [he]
  by_cases hc : cap≤ max 0 (mesh*(n : ℝ))
  · rw [min_eq_left hc]
    simp [labels]
  rw [min_eq_right (le_of_not_ge hc)]
  by_cases hn : mesh*(n : ℝ)≤0
  · rw [max_eq_left hn]
    simp [labels]
  have hn' : 0< mesh*(n : ℝ) := lt_of_not_ge hn
  rw [max_eq_right hn'.le]
  apply Finset.mem_insert_of_mem
  apply Finset.mem_insert_of_mem
  apply Finset.mem_image.mpr
  refine ⟨n,Finset.mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
  · have hh : (0 : ℝ)≤(n : ℝ) := by nlinarith
    exact_mod_cast hh
  · have hh : (n : ℝ)≤ cap/mesh := by
      apply (le_div_iff₀ hm).mpr
      have hlt : max 0 (mesh*(n : ℝ))< cap := lt_of_not_ge hc
      have : mesh*(n : ℝ)≤ max 0 (mesh*(n : ℝ)) := le_max_right _ _
      nlinarith
    exact_mod_cast hh.trans (Int.le_ceil _)

theorem squared_spike (U w cap mesh : ℝ) (Q : ℂ) (hU : 1< U) (hw : 0< w)
    (hm : 0< mesh) (hg : 0< amplitude (U^w) cap mesh Q) :
    U^(2*w*amplitude (U^w) cap mesh Q)≤‖Q‖^2 := by
  have hP : 1< U^w := Real.one_lt_rpow hU hw
  have hb := amplitude_lower (U^w) cap mesh Q hP hm hg
  have hs := (sq_le_sq₀ (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _) (norm_nonneg _)).mpr hb
  convert hs using 1 <;> first | rfl | (rw [←Real.rpow_natCast,
    ←Real.rpow_mul (Real.rpow_nonneg (by linarith : (0 : ℝ)≤ U) _),
    ←Real.rpow_mul (by linarith : (0 : ℝ)≤ U)]; congr 1; ring)

theorem product_upper {ι : Type*} (slots : Finset ι) (w : ι→ℝ) (Q : ι→ℂ)
    (U cap mesh : ℝ) (hU : 1< U) (hm : 0< mesh)
    (hw : ∀ i∈slots, 0< w i)
    (hQ : ∀ i∈slots, ‖Q i‖≤(U^(w i))^(cap+mesh)) :
    ‖∏ i∈slots, Q i‖≤ U^((∑ i∈slots, w i*amplitude (U^(w i)) cap mesh (Q i))+
      mesh*(∑ i∈slots,w i)) := by
  rw [norm_prod]
  calc
    _ ≤ ∏ i∈slots, (U^(w i))^(amplitude (U^(w i)) cap mesh (Q i)+mesh) :=
      Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i hi =>
        amplitude_upper _ cap mesh (Q i) (Real.one_lt_rpow hU (hw i hi)) hm (hQ i hi))
    _ = ∏ i∈slots, U^(w i*(amplitude (U^(w i)) cap mesh (Q i)+mesh)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact (Real.rpow_mul (by linarith : (0 : ℝ)≤ U) _ _).symm
    _ = _ := by
      rw [←Real.rpow_sum_of_pos (by linarith : 0< U)]
      congr 1
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,←Finset.sum_mul, mul_comm mesh]

theorem common_bin_selection {ι : Type*} (slots : Finset ι) (w g : ι→ℝ)
    (U δ mesh binWidth q z : ℝ) (hU : 1< U) (hδ : 0≤δ) (hmesh : 0≤ mesh)
    (hbin : 0< binWidth) (hw : ∀ i∈slots, 0< w i) (hwm : ∀ i∈slots, w i≤ mesh)
    (hg : ∀ i∈slots, 0≤ g i ∧ g i≤δ/2)
    (hq : 0≤ q) (hqδ : q≤δ/2) (hz : 0≤ z)
    (hzs : z≤∑ i∈slots,w i) (hmean : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*g i) :
    ∃ T : Finset ι, T⊆slots ∧ (∀ i∈T,0< g i) ∧ (∑ i∈T,w i)≤ z ∧
      ∀ Q : ι→ℂ, (∀ i∈slots,amplitude (U^(w i)) (δ/2) binWidth (Q i)=g i) →
        U^(2*q*z-δ*mesh)≤‖∏ i∈T,Q i‖^2 := by
  have hm : q*(∑ i∈slots,w i)≤∑ i∈slots,w i*max (g i) 0 := by
    convert hmean using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [max_eq_left (hg i hi).1]
  obtain ⟨T,hTs,hTp,hTw,hTb⟩ := HeckeDetectorSlotSelection.selected_product_spike
    slots w g U δ mesh q z hU.le hδ hmesh (fun i hi => (hw i hi).le) hwm
    (fun i hi => (hg i hi).2) hq hqδ hz hzs hm
  refine ⟨T,hTs,hTp,hTw,?_⟩
  intro Q hQ
  apply hTb Q
  intro i hi hgi
  rw [←hQ i hi] at hgi ⊢
  exact squared_spike U (w i) (δ/2) binWidth (Q i) hU (hw i hi) hbin hgi

end HeckePrimeAmplitudeBins

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Filter
open scoped Topology
namespace HeckePrimeAmplitudeBins

theorem upper_allowance_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0< dmin) (hmesh : 0< mesh) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d r cap : ℝ, dmin≤ d → rmin≤ r →
      C*(Z^d)^(cap*r+ε)≤((Z^d)^r)^(cap+mesh) := by
  have hh := HeckeDyadic.constant_absorbed_eventually C (dmin*(rmin*mesh-ε))
    (mul_pos hd (by linarith))
  filter_upwards [hh,eventually_ge_atTop (1 : ℝ)] with Z hC hZ
  intro d r cap hd' hr'
  have hZp : 0< Z := by linarith
  have hU : 0< Z^d := Real.rpow_pos_of_pos hZp _
  have hgr : rmin*mesh-ε≤ r*mesh-ε := by nlinarith
  have hexp : dmin*(rmin*mesh-ε)≤ d*(r*mesh-ε) :=
    mul_le_mul hd' hgr (by linarith) (hd.trans_le hd').le
  have hc : C≤(Z^d)^(r*mesh-ε) := by
    apply hC.trans
    rw [←Real.rpow_mul hZp.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ hexp
  calc
    _ ≤ (Z^d)^(r*mesh-ε)*(Z^d)^(cap*r+ε) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hU.le _)
    _ = ((Z^d)^r)^(cap+mesh) := by
      rw [←Real.rpow_add hU,←Real.rpow_mul hU.le]
      congr 1
      ring

theorem actual_bins_eventually (C dmin rmin ε mesh : ℝ)
    (hd : 0< dmin) (hr : 0< rmin) (hmesh : 0< mesh) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤ d → ∀ r cap : ℝ, rmin≤ r → 0≤ cap →
      ∀ Q : ℂ, ‖Q‖≤ C*(Z^d)^(cap*r+ε) →
      0≤ amplitude ((Z^d)^r) cap mesh Q ∧
      amplitude ((Z^d)^r) cap mesh Q≤ cap ∧
      amplitude ((Z^d)^r) cap mesh Q∈labels cap mesh ∧
      ‖Q‖≤((Z^d)^r)^(amplitude ((Z^d)^r) cap mesh Q+mesh) ∧
      (0< amplitude ((Z^d)^r) cap mesh Q →
        (Z^d)^(2*r*amplitude ((Z^d)^r) cap mesh Q)≤‖Q‖^2) := by
  filter_upwards [upper_allowance_eventually C dmin rmin ε mesh hd hmesh hgap,
    eventually_gt_atTop (1 : ℝ)] with Z hallow hZ
  intro d hd' r cap hr' hcap Q hQ
  have hU : 1< Z^d := Real.one_lt_rpow hZ (hd.trans_le hd')
  have hP : 1<(Z^d)^r := Real.one_lt_rpow hU (hr.trans_le hr')
  have hb := amplitude_bounds ((Z^d)^r) cap mesh Q hcap
  exact ⟨hb.1,hb.2,amplitude_mem_labels _ cap mesh Q hmesh,
    amplitude_upper _ cap mesh Q hP hmesh (hQ.trans (hallow d r cap hd' hr')),
    squared_spike (Z^d) r cap mesh Q hU (hr.trans_le hr') hmesh⟩

end HeckePrimeAmplitudeBins

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace HeckePrimeAmplitudeActual
open HeckeFamily HeckePrimeRay HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem ray_amplitude_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0< A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0< e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤ d → d≤ dmax → 2≤ Z^d → 2< Z^τ →
    ∀ (χ : Character) (hχ : ∀ θ : RayQuotient.Characters M H,
      (twistedFamily M H hH χ θ).residue≠1) (a : ℝ) (i : ℕ),
      51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum (twistedFamily M H hH χ) hχ (3*(i+1 : ℕ)*Z^τ)< a+2*e →
    ∀ r σ freq : ℝ, rmin≤ r → r≤ R → σmin≤σ → σ≤σmax →
      (∀ θ : RayQuotient.Characters M H,(twistedFamily M H hH χ θ).modulus.absNorm≤ Z^d) →
      |freq|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := rayPrimePolynomial M H χ W B ((Z^d)^r) σ freq
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤ g ∧ g≤ a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0< g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  obtain ⟨C,hC,hbound⟩ := ray_prime_bin_bound M H hH W A B hA hWs hW
    R dmax τ ε e κ η σmin σmax hR hdmax hτ hε he he' hκ hη hbudget
  have hbins := actual_bins_eventually C dmin rmin ε mesh hdmin hrmin hmesh hgap
  have hlog := HeckePrimeScale.log_scale_eventually dmin rmin
    (2*(|Real.log A|+|Real.log B|)+1) hdmin hrmin
  filter_upwards [hbins,hlog,eventually_ge_atTop (1 : ℝ)] with Z hb hl hZ
  intro d hd hd' hU hT χ hχ a i ha ha' hmax r σ freq hr hr' hσ hσ' hQ hf ht
  have hestimate := hbound Z d hZ (hdmin.trans_le hd).le hd' hU hT χ hχ a i
    ha ha' hmax r σ freq (hrmin.trans_le hr).le hr' hσ hσ' (hl d r hd hr) hQ hf ht
  exact hb d hd r (a-1/2) hr (by linarith) _ hestimate

end HeckePrimeAmplitudeActual

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace HeckeDetectorPhysicalBins
open HeckeFamily HeckeDetectorPrimeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem physical_bins (W : ℝ→ℂ) (A B : ℝ) (hA : 0< A)
    (hWs : Function.support W⊆Icc A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ η mesh σmin σmax : ℝ)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0< e) (he' : e<1/1000)
    (hκ : 0<κ) (hη : 0≤η) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) :
    ∀ᶠ Z : ℝ in atTop, ∀ d : ℝ, dmin≤ d → d≤ dmax → 2≤ Z^d → 2< Z^τ →
    ∀ (data : RowData M) (cert : Ramification M data) (a : ℝ) (i : ℕ),
      51/100≤ a → a≤1 →
      HeckeDetectorZeros.zeroMaximum
        (HeckePrimeRay.twistedFamily M H hH (data.character M))
        (cert.nonprincipal M H hH) (3*(i+1 : ℕ)*Z^τ)< a+2*e →
    ∀ (r : ℝ) (z : ℂ), rmin≤ r → r≤ R → σmin≤1-z.re → 1-z.re≤σmax →
      M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
        (Ideal.span {data.u}).absNorm≤ Z^d →
      |z.im|+Z^τ/2≤(3*i+2 : ℕ)*Z^τ → (3+(3*i+2 : ℕ)*Z^τ)^2≤(Z^d)^η →
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H data.u W B ((Z^d)^r) z
    let g := amplitude ((Z^d)^r) (a-1/2) mesh Q
    0≤ g ∧ g≤ a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤((Z^d)^r)^(g+mesh) ∧ (0< g → (Z^d)^(2*r*g)≤‖Q‖^2) := by
  have hh := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA hWs hW
    R dmin dmax rmin τ ε e κ η mesh σmin σmax hR hdmin hdmax hrmin
    hτ hε he he' hκ hη hmesh hbudget hgap
  filter_upwards [hh] with Z hZ
  intro d hd hd' hU hT data cert a i ha ha' hnext r z hr hr' hs hs' hQ hf ht
  have hQ' (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤ Z^d := by
    have hb := data.twisted_conductor M H hH θ
    have hb' : ((HeckePrimeRay.twistedFamily M H hH (data.character M) θ).modulus.absNorm : ℝ)≤
        ((M.absNorm^2*(Ideal.span {data.m}).absNorm*(Ideal.span {(72 : O)}).absNorm*
          (Ideal.span {data.u}).absNorm : ℕ) : ℝ) := by exact_mod_cast hb
    exact hb'.trans (by exact_mod_cast hQ)
  have hb := hZ d hd hd' hU hT (data.character M) (cert.nonprincipal M H hH)
    a i ha ha' hnext r (1-z.re) z.im hr hr' hs hs' hQ' hf ht
  simpa only [data.amplitude_eq M H hH] using hb

end HeckeDetectorPhysicalBins

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorRelativePrime
open HeckeFamily HeckeDetectorPrimeFamily

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
theorem relative_coefficient_on_ray (ν χ : Character) (hM : M≤ν.modulus)
    (J : Ideal O) (hJ : J∈RayQuotient.identityClass M H) :
    idealCoeff ((ν.product χ).product ν.inverse) J=idealCoeff χ J := by
  have hn := idealCoeff_ne_zero_of_coprime ν J hJ.1
    (HeckePrimeRow.identityClass_coprime_larger M H hJ hM)
  rw [idealCoeff_product,idealCoeff_product,idealCoeff_inverse]
  field_simp

theorem physical_eq_relative_average (data : RowData M) (ν : Character)
    (hM : M≤ν.modulus) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H data.u W b D z=
      (RayQuotient.classNumber M H : ℂ)⁻¹ *
        ∑ θ : RayQuotient.Characters M H,
          HeckePrimeAnnular.primePolynomial
            ((ν.product (data.character M)).product
              (ν.inverse.product (HeckeRayQuotient.character M H hH θ)))
            W b D (1-z.re) z.im := by
  rw [data.amplitude_eq M H hH]
  have he : HeckePrimeRay.rayPrimePolynomial M H (data.character M) W b D (1-z.re) z.im=
      HeckePrimeRay.rayPrimePolynomial M H ((ν.product (data.character M)).product ν.inverse)
        W b D (1-z.re) z.im := by
    unfold HeckePrimeRay.rayPrimePolynomial
    congr 1
    apply Finset.sum_congr rfl
    intro J hJ
    rw [relative_coefficient_on_ray M H ν (data.character M) hM J (Finset.mem_filter.mp hJ).2.2]
  rw [he,HeckePrimeRay.rayPrimePolynomial_eq_average M H hH]
  congr 1
  apply Finset.sum_congr rfl
  intro θ hθ
  unfold HeckePrimeAnnular.primePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro J hJ
  simp only [HeckePrimeRay.twistedFamily,idealCoeff_product]
  ring

end HeckeDetectorRelativePrime

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

def physical {Row Slot : Type*} (row : Row→O) (W : Slot→ℝ→ℂ)
    (b w : Slot→ℝ) (z : Slot→ℂ) (U : ℝ) (u : Row) (s : Slot) : ℂ :=
  HeckePrimeRow.canonicalPrimeAmplitude M H (row u) (W s) (b s) (U^(w s)) (z s)

def weightedMean {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ) : ℝ :=
  (∑ s∈slots,w s*g s)/(∑ s∈slots,w s)

theorem weightedMean_bounds {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ)
    (δ : ℝ) (hw : ∀ s∈slots,0≤ w s) (hL : 0<∑ s∈slots,w s)
    (hg : ∀ s∈slots,0≤ g s ∧ g s≤δ/2) :
    0≤ weightedMean slots w g ∧ weightedMean slots w g≤δ/2 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun s hs => mul_nonneg (hw s hs) (hg s hs).1)) hL.le
  · apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ ∑ s∈slots,w s*(δ/2) := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_left (hg s hs).2 (hw s hs))
      _ = _ := by rw [←Finset.sum_mul]; ring

omit [NeZero M] in
theorem select_physical_product {Row Slot : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b w g : Slot→ℝ)
    (zs : Slot→ℂ) (U δ mesh binWidth z : ℝ)
    (hU : 1< U) (hδ : 0≤δ) (hmesh : 0≤ mesh) (hbin : 0< binWidth)
    (hw : ∀ s∈slots,0< w s) (hwm : ∀ s∈slots,w s≤ mesh)
    (hL : 0<∑ s∈slots,w s) (hz : 0≤ z) (hzL : z≤∑ s∈slots,w s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      amplitude (U^(w s)) (δ/2) binWidth (physical M H row W b w zs U u s)=g s) :
    ∃ selected : Finset Slot, selected⊆slots ∧ (∀ s∈selected,0< g s) ∧
      (∑ s∈selected,w s)≤ z ∧
      ∀ u∈rows, U^(2*weightedMean slots w g*z-δ*mesh)≤
        ‖∏ s∈selected,physical M H row W b w zs U u s‖^2 := by
  obtain ⟨u0,hu0⟩ := hne
  have hg (s : Slot) (hs : s∈slots) : 0≤ g s ∧ g s≤δ/2 := by
    rw [←hbins u0 hu0 s hs]
    exact amplitude_bounds _ _ _ _ (by positivity)
  obtain ⟨hq,hqδ⟩ := weightedMean_bounds slots w g δ (fun s hs => (hw s hs).le) hL hg
  have hm : weightedMean slots w g*(∑ s∈slots,w s)≤∑ s∈slots,w s*g s := by
    unfold weightedMean
    rw [div_mul_cancel₀ _ hL.ne']
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := common_bin_selection slots w g U δ mesh binWidth
    (weightedMean slots w g) z hU hδ hmesh hbin hw hwm hg hq hqδ hz hzL hm
  exact ⟨selected,hsub,hpositive,hlen,fun u hu => hspike _ (hbins u hu)⟩

end HeckeDetectorPhysicalSelection

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
open Set
namespace HeckeDetectorFiberSpikes
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem fiber_spikes {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1< U) (ha : 0≤ a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(w u).label=label)
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    ∀ u∈rows,
      (w u).zero.re∈Icc (0 : ℝ) 1 ∧
      |(w u).frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T ∧
      U^((2*a-1)*r-2*ε)≤
        ‖polynomial (χ u label) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
          (U^r) (w u).zero.re (w u).frequency‖^2 ∧
      U^((2*a-1)*m-2*ε)≤
        ‖polynomial (χ u label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2 := by
  dsimp only
  intro u hu
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by rw [(w u).left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by rw [(w u).right_exponent hU,hK u hu]
  refine ⟨⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩,(w u).frequency_bound,?_,?_⟩
  · simpa only [hr,hlabel u hu,Witness.frequency] using (w u).inverse_spike
  · simpa only [hm,hlabel u hu,Witness.frequency] using (w u).plain_spike

end HeckeDetectorFiberSpikes

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0< U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤ C*U^b) :
    (rows.card : ℝ)≤ C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤ C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

theorem inverse_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (D : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ r q z εw εp εm C : ℝ) (hU : 0< U)
    (hM : ∀ u∈rows, U^(δ*r-εw)≤‖polynomial (χ u) true W D (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2≤ C*U^(1+εm)) :
    (rows.card : ℝ)≤ C*U^(1-δ*r-2*q*z+εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*r-εw)+(2*q*z-εp))≤‖polynomial (χ u) true W D (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,norm_mul,mul_pow]
    exact mul_le_mul (hM u hu) (hP u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _)
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem plain_count {α : Type*} (rows : Finset α) (χ : α→Character)
    (W : ℝ→ℂ) (N : ℝ) (σ freq : α→ℝ) (P : α→ℂ)
    (U δ m q z εw εp εm C : ℝ) (hU : 0< U)
    (hS : ∀ u∈rows, U^(δ*m-εw)≤‖polynomial (χ u) false W N (σ u) (freq u)‖^2)
    (hP : ∀ u∈rows, U^(2*q*z-εp)≤‖P u‖^2)
    (henergy : ∑ u∈rows,
      ‖polynomial (χ u) false W N (σ u) (freq u)*
        polynomial (χ u) false W N (σ u) (freq u)*P u‖^2≤ C*U^(1+εm)) :
    (rows.card : ℝ)≤ C*U^(1-2*δ*m-2*q*z+2*εw+εp+εm) := by
  have hs (u : α) (hu : u∈rows) :
      U^((δ*m-εw)+(δ*m-εw)+(2*q*z-εp))≤
        ‖polynomial (χ u) false W N (σ u) (freq u)*
          polynomial (χ u) false W N (σ u) (freq u)*P u‖^2 := by
    rw [Real.rpow_add hU,Real.rpow_add hU,norm_mul,norm_mul,mul_pow,mul_pow]
    exact mul_le_mul (mul_le_mul (hS u hu) (hS u hu) (Real.rpow_nonneg hU.le _) (sq_nonneg _))
      (hP u hu) (Real.rpow_nonneg hU.le _) (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hh := card_of_energy rows _ U _ (1+εm) C hU hs henergy
  convert hh using 1; congr 2; ring

theorem classified_card_bound {α Label : Type*} [Fintype Label]
    (rows : Finset α) (presentation : α→Label) (left right : α→ℕ)
    (B : ℕ) (hleft : ∀ u∈rows, left u< B) (hright : ∀ u∈rows, right u< B)
    (K : ℝ)
    (hfiber : ∀ p : Label, ∀ j∈Finset.range B, ∀ k∈Finset.range B,
      ((rows.filter (fun u => presentation u=p ∧ left u=j ∧ right u=k)).card : ℝ)≤ K) :
    (rows.card : ℝ)≤(Fintype.card Label : ℝ)*(B : ℝ)^2*K := by
  let labels : Finset (Label×ℕ×ℕ) := Finset.univ ×ˢ (Finset.range B ×ˢ Finset.range B)
  let label : α→Label×ℕ×ℕ := fun u => (presentation u,left u,right u)
  have hmaps : (rows : Set α).MapsTo label labels := by
    intro u hu
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (hleft u hu),Finset.mem_range.mpr (hright u hu)⟩⟩
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  have he' : (rows.card : ℝ)=∑ l∈labels,
      ((rows.filter (fun u => label u=l)).card : ℝ) := by exact_mod_cast he
  rw [he']
  calc
    _ ≤ ∑ l∈labels, K := by
      apply Finset.sum_le_sum
      intro l hl
      rcases l with ⟨p,j,k⟩
      obtain ⟨hp,hjk⟩ := Finset.mem_product.mp hl
      obtain ⟨hj,hk⟩ := Finset.mem_product.mp hjk
      have hh := hfiber p j hj k hk
      simpa only [label,Prod.mk.injEq] using hh
    _ = _ := by simp [labels,Finset.card_product,pow_two,mul_assoc]

end HeckeDetectorRowCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Set
namespace HeckeDetectorFiberEnergy
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorRowwisePolynomial

theorem inverse_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤ a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0< D) (hwb : 0≤ wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤ E)
    (height : ℝ) (hh : 0≤ height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hraw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) true ((logProfile^[n]) W) D s t*P u‖^2≤ E) :
    ∑ u∈rows,‖polynomial (χ u label) true W D (w u).zero.re (w u).frequency*P u‖^2≤
      12*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwiseMarked.marked_rowwise rows (fun u => χ u label) true W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf
    (by simpa using hraw 0 (by omega)) (by simpa using hraw 1 (by omega))
    (by simpa using hraw 2 (by omega))
  refine hb.trans ?_
  nlinarith

theorem plain_energy {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (ha : 0≤ a)
    (w : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (W : ℝ→ℂ) (D wa wb E : ℝ) (P : Row→ℂ)
    (hD : 0< D) (hwb : 0≤ wb) (hs : Function.support W⊆Icc wa wb) (hE : 0≤ E)
    (height : ℝ) (hh : 0≤ height) (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) W) D s t*
        polynomial (χ u label) false ((logProfile^[k]) W) D s t*P u‖^2≤ E) :
    ∑ u∈rows,‖polynomial (χ u label) false W D (w u).zero.re (w u).frequency*
      polynomial (χ u label) false W D (w u).zero.re (w u).frequency*P u‖^2≤
      192*(1+height)*E := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log D) wb
  have hcover : ∀ J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/D)≠0 → J∈S := by
    simpa only [Real.exp_log hD] using HeckeInverseAmplification.scaleSupport_cover
      W wa wb (Real.log D) (Real.log D) hwb hs (le_refl _)
  have hσ (u : Row) (hu : u∈rows) : (w u).zero.re∈Icc (0 : ℝ) 1 :=
    ⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩
  have hf (u : Row) (hu : u∈rows) : (w u).frequency∈Icc (-height) height :=
    abs_le.mp ((w u).frequency_bound.trans hfreq)
  have hb := HeckeDetectorRowwisePlain.plain_squared_rowwise rows (fun u => χ u label) W D hD S hcover
    P 0 1 (-height) height E (by norm_num) (by linarith) hE (fun u => (w u).zero.re)
    (fun u => (w u).frequency) hσ hf hraw
  refine hb.trans ?_
  nlinarith

end HeckeDetectorFiberEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Set
namespace HeckeDetectorInverseFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial

def inverseTest (U tstar r : ℝ) : ℝ→ℂ :=
  HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r)

variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem inverse_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1< U) (ha : 1/2≤ a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b widths g : Slot→ℝ) (zs : Slot→ℂ)
    (mesh binWidth z εm C height : ℝ) (hmesh : 0≤ mesh) (hbin : 0< binWidth)
    (hw : ∀ s∈slots,0< widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤ z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (physical M H row W b widths zs U u s)=g s)
    (hC : 0≤ C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hcap1 : Real.logb U ((2 : ℝ)^J.val)+2*z<1)
    (hcap2 : 2*Real.logb U ((2 : ℝ)^J.val)+8*z<3)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      Real.logb U ((2 : ℝ)^J.val)+2*(∑ s∈selected,widths s)<1 →
      2*Real.logb U ((2 : ℝ)^J.val)+8*(∑ s∈selected,widths s)<3 →
      ∀ n : ℕ,n≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) true
          ((logProfile^[n]) (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val))))
          (U^(Real.logb U ((2 : ℝ)^J.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤ C*U^(1+εm)) :
    (rows.card : ℝ)≤(12*(1+height)*C)*
      U^(1-(2*a-1)*Real.logb U ((2 : ℝ)^J.val)-2*weightedMean slots widths g*z+
        2*ε+(2*a-1)*mesh+εm) := by
  let r := Real.logb U ((2 : ℝ)^J.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_physical_product M H rows hne slots
    row W b widths g zs U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap1' : r+2*(∑ s∈selected,widths s)<1 := by dsimp [r]; linarith
  have hcap2' : 2*r+8*(∑ s∈selected,widths s)<3 := by dsimp [r]; linarith
  have hUp : 0< U := zero_lt_one.trans hU
  have hDp : 0< U^r := Real.rpow_pos_of_pos hUp _
  have hE : 0≤ C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.inverse_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label (inverseTest U tstar r) (U^r) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s) hDp (by norm_num)
    (HeckeDetectorDyadicActual.inverse_profile_support _ _) hE height hheight hfreq
    (hraw selected hsub hcap1' hcap2')
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) true (inverseTest U tstar r) (U^r) (witness u).zero.re
        (witness u).frequency*(∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤
      (12*(1+height)*C)*U^(1+εm) := by
    convert he using 1 <;> first | rfl | ring
  exact HeckeDetectorRowCount.inverse_count rows (fun u => χ u label)
    (inverseTest U tstar r) (U^r) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s)
    U (2*a-1) r (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (12*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.1) hspike he'

end HeckeDetectorInverseFiberCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Set
namespace HeckeDetectorPlainFiberCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem plain_fiber_count {Row Label Slot : Type*}
    (rows : Finset Row) (hne : rows.Nonempty) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1< U) (ha : 1/2≤ a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (slots : Finset Slot) (row : Row→O) (W : Slot→ℝ→ℂ) (b widths g : Slot→ℝ) (zs : Slot→ℂ)
    (mesh binWidth z κplain εm C height : ℝ) (hmesh : 0≤ mesh) (hbin : 0< binWidth)
    (hw : ∀ s∈slots,0< widths s) (hwm : ∀ s∈slots,widths s≤ mesh)
    (hL : 0<∑ s∈slots,widths s) (hz : 0≤ z) (hzL : z≤∑ s∈slots,widths s)
    (hbins : ∀ u∈rows,∀ s∈slots,
      HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
        (physical M H row W b widths zs U u s)=g s)
    (hκ : 0≤κplain) (hC : 0≤ C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hcap : 2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*z≤1)
    (hraw : ∀ selected : Finset Slot, selected⊆slots →
      2*Real.logb U ((2 : ℝ)^K.val)+6*κplain*(∑ s∈selected,widths s)≤1 →
      ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
        ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
          polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
          (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
            (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤ C*U^(1+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(1-2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)-2*weightedMean slots widths g*z+
        4*ε+(2*a-1)*mesh+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hδ : 0≤2*a-1 := by linarith
  obtain ⟨selected,hsub,hpositive,hlen,hspike⟩ := select_physical_product M H rows hne slots
    row W b widths g zs U (2*a-1) mesh binWidth z hU hδ hmesh hbin hw hwm hL hz hzL hbins
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hcap' : 2*m+6*κplain*(∑ s∈selected,widths s)≤1 := by
    have hh := mul_le_mul_of_nonneg_left hlen (show 0≤6*κplain by positivity)
    dsimp [m]
    linarith
  have hUp : 0< U := zero_lt_one.trans hU
  have hDp : 0< U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤ C*U^(1+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i
    (by linarith) witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(1+εm))
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s) hDp (by norm_num)
    positiveAnnular_support hE height hheight hfreq (hraw selected hsub hcap')
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        (∏ s∈selected,physical M H row W b widths zs U u s)‖^2≤
      (192*(1+height)*C)*U^(1+εm) := by
    convert he using 1 <;> first | rfl | ring
  have hc := HeckeDetectorRowCount.plain_count rows (fun u => χ u label)
    positiveAnnular (U^m) (fun u => (witness u).zero.re) (fun u => (witness u).frequency)
    (fun u => ∏ s∈selected,physical M H row W b widths zs U u s)
    U (2*a-1) m (weightedMean slots widths g) z (2*ε) ((2*a-1)*mesh) εm
    (192*(1+height)*C) hUp (fun u hu => (hsp u hu).2.2.2) hspike he'
  convert hc using 1; congr 2; ring

end HeckeDetectorPlainFiberCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace HeckeDetectorNoSlotInverseCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount

theorem no_slot_inverse_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (R εm : ℝ) (hR : 0≤ R) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ {Label : Type*} (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
        (a ε tstar T allowance : ℝ) (i : ℕ), 1< U → 1/2≤ a →
      ∀ (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
        (label : Label) (J K : Fin (dyadicLength U)),
      (∀ u∈rows,(witness u).label=label) →
      (∀ u∈rows,(witness u).left=J) → (∀ u∈rows,(witness u).right=K) →
      0≤ Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val)≤ R →
      ∀ (data : RowData) (reverse : Bool) (C height : ℝ),0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      (∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤ U) →
      (∀ u∈rows,∀ I : Ideal O,idealCoeff (χ u label) I=
        if reverse then starRingEnd ℂ (idealCoeff (data.character ⟨u.val,u.property.1⟩) I)
        else idealCoeff (data.character ⟨u.val,u.property.1⟩) I) →
      (∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
        let W := twistProfile (logTest
          (orientedProfile reverse (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val)))) n) s t
        RawMoment data W c κ C ∧ RawMoment data (scaleProfile W) c κ C) →
      (rows.card : ℝ)≤(12*(1+height)*(C*K₀))*
        U^(sourceExponent (Real.logb U ((2 : ℝ)^J.val))-
          (2*a-1)*Real.logb U ((2 : ℝ)^J.val)+2*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,he⟩ := no_slot_rowwise_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB R εm hR hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he] with U he
  intro Label rows χ a ε tstar T allowance i hU ha witness label J K hlabel hJ hK hr hrR
    data reverse C height hC hheight hfreq hrows hcoeff hraw
  let r := Real.logb U ((2 : ℝ)^J.val)
  let V := orientedProfile reverse (inverseTest U tstar r)
  have hUp : 0< U := zero_lt_one.trans hU
  have hD : 0< U^r := Real.rpow_pos_of_pos hUp _
  have hbase := HeckeDetectorDyadicActual.inverse_profile_support (U^tstar) (U^r)
  have hs : Function.support V⊆Icc (1/4 : ℝ) (9/4) := by
    cases reverse
    · exact hbase
    · simpa only [V,orientedProfile,Bool.true_eq,ite_true,conjugate_profile_support,inverseTest] using hbase
  have hb := HeckeDetectorDyadicActual.inverse_profile_smooth (U^tstar) (U^r)
  have hV : ContDiff ℝ ∞ V := by
    cases reverse
    · exact hb
    · exact conjugate_profile_smooth _ hb
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hσ (u : FreeRow) (hu : u∈rows) : (witness u).zero.re∈Icc (0 : ℝ) 1 := (hsp u hu).1
  have hf (u : FreeRow) (hu : u∈rows) :
      orientedFrequency reverse (witness u).frequency∈Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact (hsp u hu).2.1.trans hfreq
  have hen := he r data rows V (1/4) (9/4) C height (fun u => (witness u).zero.re)
    (fun u => orientedFrequency reverse (witness u).frequency)
    hr hrR hC hheight (by norm_num) (by norm_num) hs hV hrows hσ hf hraw
  have hspike (u : FreeRow) (hu : u∈rows) : U^((2*a-1)*r-2*ε)≤
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2 := by
    have hh := (hsp u hu).2.2.1
    rw [norm_of_oriented_coefficients (χ u label) (data.character ⟨u.val,u.property.1⟩)
      reverse (hcoeff u hu) true _ _ _ _ hD] at hh
    exact hh
  have hen' : ∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2≤
      (12*(1+height)*(C*K₀))*U^(sourceExponent r+εm) := by
    convert hen using 1 <;> first | rfl | ring
  have hc' := HeckeDetectorRowCount.card_of_energy rows _ U ((2*a-1)*r-2*ε)
    (sourceExponent r+εm) (12*(1+height)*(C*K₀)) hUp hspike hen'
  convert hc' using 1; congr 2; ring

end HeckeDetectorNoSlotInverseCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Set
namespace HeckeDetectorNoSlotPlainCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial

theorem no_slot_plain_count {Row Label : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1< U) (ha : 0≤ a)
    (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(witness u).label=label)
    (hJ : ∀ u∈rows,(witness u).left=J) (hK : ∀ u∈rows,(witness u).right=K)
    (εm C height : ℝ) (hC : 0≤ C) (hheight : 0≤ height)
    (hfreq : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (hraw : ∀ j k : ℕ,j+k≤2 → ∀ σ∈Icc (0 : ℝ) 1,∀ freq∈Icc (-height) height,
      ∑ u∈rows,‖polynomial (χ u label) false ((logProfile^[j]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq*
        polynomial (χ u label) false ((logProfile^[k]) positiveAnnular)
        (U^(Real.logb U ((2 : ℝ)^K.val))) σ freq‖^2≤
          C*U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))+εm)) :
    (rows.card : ℝ)≤(192*(1+height)*C)*
      U^(max 1 (2*Real.logb U ((2 : ℝ)^K.val))-
        2*(2*a-1)*Real.logb U ((2 : ℝ)^K.val)+4*ε+εm) := by
  let m := Real.logb U ((2 : ℝ)^K.val)
  have hUp : 0< U := zero_lt_one.trans hU
  have hDp : 0< U^m := Real.rpow_pos_of_pos hUp _
  have hE : 0≤ C*U^(max 1 (2*m)+εm) := mul_nonneg hC (Real.rpow_nonneg hUp.le _)
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU ha
    witness label J K hlabel hJ hK
  have he := HeckeDetectorFiberEnergy.plain_energy rows χ U a ε tstar T allowance i ha
    witness label positiveAnnular (U^m) (1/4) (9/4) (C*U^(max 1 (2*m)+εm))
    (fun _ => 1) hDp (by norm_num) positiveAnnular_support hE height hheight hfreq
    (by simpa only [mul_one] using hraw)
  simp only [mul_one] at he
  have hs (u : Row) (hu : u∈rows) : U^(2*((2*a-1)*m-2*ε))≤
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2 := by
    rw [show 2*((2*a-1)*m-2*ε)=((2*a-1)*m-2*ε)+((2*a-1)*m-2*ε) by ring,
      Real.rpow_add hUp,norm_mul,mul_pow]
    exact mul_le_mul (hsp u hu).2.2.2 (hsp u hu).2.2.2
      (Real.rpow_nonneg hUp.le _) (sq_nonneg _)
  have he' : ∑ u∈rows,
      ‖polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency*
        polynomial (χ u label) false positiveAnnular (U^m) (witness u).zero.re (witness u).frequency‖^2≤
      (192*(1+height)*C)*U^(max 1 (2*m)+εm) := by convert he using 1 <;> first | rfl | ring
  have hh := HeckeDetectorRowCount.card_of_energy rows _ U (2*((2*a-1)*m-2*ε))
    (max 1 (2*m)+εm) (192*(1+height)*C) hUp hs he'
  convert hh using 1; congr 2; ring

end HeckeDetectorNoSlotPlainCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set
namespace HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

/-- A fiber fixes the witness label, dyadic scales and prime-amplitude bins. -/
structure Fiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  nonempty : rows.Nonempty
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  label : Label
  left : Fin (dyadicLength U)
  right : Fin (dyadicLength U)
  fixed_label : ∀ u∈rows,(witness u).label=label
  fixed_left : ∀ u∈rows,(witness u).left=left
  fixed_right : ∀ u∈rows,(witness u).right=right
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤ U
  rowData : RowData
  reverse : Bool
  row_coeff : ∀ u∈rows,∀ J : Ideal O,idealCoeff (family u label) J=
    if reverse then starRingEnd ℂ (idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J)
    else idealCoeff (rowData.character ⟨u.val,u.property.1⟩) J
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  bin : Slot→ℝ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤ mesh
  binWidth_pos : 0< binWidth
  widths_pos : ∀ s∈slots,0< widths s
  widths_mesh : ∀ s∈slots,widths s≤ mesh
  supply : 7/37≤∑ s∈slots,widths s
  fixed_bin : ∀ u∈rows,∀ s∈slots,
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) binWidth
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U u s)=bin s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def Fiber.r (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.left.val)
def Fiber.m (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := Real.logb U ((2 : ℝ)^F.right.val)
def Fiber.q (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ := weightedMean F.slots F.widths F.bin
def Fiber.inverseProfile (F : Fiber M H Label Slot U a ε tstar T allowance i) : ℝ→ℂ := inverseTest U tstar F.r
def Fiber.physicalProduct (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (selected : Finset Slot) (u : FreeRow) : ℂ :=
  ∏ s∈selected,physical M H (fun u : FreeRow => u.val) F.profile F.upper F.widths F.external U u s

/-- The four moment estimates used in the detector fiber count. -/
structure Moments (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (Δ c κ C height εm : ℝ) : Prop where
  inverse_raw : ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
    let W := twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t
    RawMoment F.rowData W c κ C ∧ RawMoment F.rowData (scaleProfile W) c κ C
  inverse_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    F.r+2*(∑ s∈selected,F.widths s)<1 → 2*F.r+8*(∑ s∈selected,F.widths s)<3 →
    ∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) true ((logProfile^[n]) F.inverseProfile)
        (U^F.r) s t*F.physicalProduct selected u‖^2≤ C*U^(1+εm)
  plain_marked : ∀ selected : Finset Slot,selected⊆F.slots →
    2*F.m+6*(3/4+2*Δ)*(∑ s∈selected,F.widths s)≤1 →
    ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t*
          F.physicalProduct selected u‖^2≤ C*U^(1+εm)
  plain_unmarked : ∀ j k : ℕ,j+k≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
      ∑ u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) s t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) s t‖^2≤
          C*U^(max 1 (2*F.m)+εm)

theorem Fiber.mean_bounds (F : Fiber M H Label Slot U a ε tstar T allowance i) (ha : 1/2≤ a) :
    0≤ F.q ∧ F.q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := F.nonempty
  apply weightedMean_bounds F.slots F.widths F.bin (2*a-1)
    (fun s hs => (F.widths_pos s hs).le) (by linarith [F.supply])
  intro s hs
  rw [←F.fixed_bin u hu s hs]
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

end HeckeDetectorRawFiber

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

abbrev BinLabel {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ) :=
  slots → ↥(HeckePrimeAmplitudeBins.labels cap mesh)

def amplitudeLabel {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0< mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : BinLabel slots cap mesh :=
  fun s => ⟨HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s),
    HeckePrimeAmplitudeBins.amplitude_mem_labels _ _ _ _ hm⟩

def fiber {Row Label Slot : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u=bin ∧
    (w u).label=label ∧ (w u).left=J ∧ (w u).right=K)

theorem card_eq_sum_fibers {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots ((2*a-1)/2) mesh, ∑ label : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        (fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => (amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u,
      (w u).label,(w u).left,(w u).right)) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

def binValue {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (bin : BinLabel slots cap mesh) (s : Slot) : ℝ :=
  if hs : s∈slots then (bin ⟨s,hs⟩).val else 0

theorem fixed_bin {Row Label Slot : Type*}
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) (bin : BinLabel slots ((2*a-1)/2) mesh)
    (label : Label) (J K : Fin (dyadicLength U)) (u : Row)
    (hu : u∈fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K)
    (s : Slot) (hs : s∈slots) :
    HeckePrimeAmplitudeBins.amplitude (U^(widths s)) ((2*a-1)/2) mesh (physical u s)=
      binValue slots ((2*a-1)/2) mesh bin s := by
  have he := (Finset.mem_filter.mp hu).2.1
  have hv := congrArg (fun f : BinLabel slots ((2*a-1)/2) mesh => (f ⟨s,hs⟩).val) he
  simpa only [amplitudeLabel,binValue,dif_pos hs] using hv

def toFiber (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) {Label Slot : Type*}
    (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (hrow : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤ U)
    (data : Label→RowData) (reverse : Label→Bool)
    (hcoeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (χ u j) I=
      if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
      else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hmesh : 0≤ mesh) (hbw : 0< binWidth)
    (hw : ∀ s∈slots,0< widths s) (hwmesh : ∀ s∈slots,widths s≤ mesh)
    (hsupply : 7/37≤∑ s∈slots,widths s)
    (bin : BinLabel slots ((2*a-1)/2) binWidth) (label : Label)
    (J K : Fin (dyadicLength U))
    (hne : (fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
      (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K).Nonempty) :
    Fiber M H Label Slot U a ε tstar T allowance i where
  rows := fiber rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K
  nonempty := hne
  family := χ
  witness := w
  label := label
  left := J
  right := K
  fixed_label := fun _u hu => (Finset.mem_filter.mp hu).2.2.1
  fixed_left := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.1
  fixed_right := fun _u hu => (Finset.mem_filter.mp hu).2.2.2.2
  row_norm := fun u hu => hrow u (Finset.mem_filter.mp hu).1
  rowData := data label
  reverse := reverse label
  row_coeff := fun u hu => hcoeff u (Finset.mem_filter.mp hu).1 label
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  bin := binValue slots ((2*a-1)/2) binWidth bin
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hmesh
  binWidth_pos := hbw
  widths_pos := hw
  widths_mesh := hwmesh
  supply := hsupply
  fixed_bin := fun u hu s hs => fixed_bin rows χ U a ε tstar T allowance i w slots binWidth hbw widths
    (physical M H (fun u : FreeRow => u.val) profile upper widths external U) bin label J K u hu s hs

end HeckeDetectorFiberPartition

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorFiberPartition
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

structure Batch (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ) (Label Slot : Type*)
    (U a ε tstar T allowance : ℝ) (i : ℕ) where
  rows : Finset FreeRow
  family : FreeRow→Label→Character
  witness : ∀ u,SupportedWitness (family u) U a ε tstar T allowance i
  row_norm : ∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤ U
  data : Label→RowData
  reverse : Label→Bool
  row_coeff : ∀ u∈rows,∀ j,∀ I : Ideal O,idealCoeff (family u j) I=
    if reverse j then starRingEnd ℂ (idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I)
    else idealCoeff ((data j).character ⟨u.val,u.property.1⟩) I
  slots : Finset Slot
  profile : Slot→ℝ→ℂ
  upper : Slot→ℝ
  widths : Slot→ℝ
  external : Slot→ℂ
  mesh : ℝ
  binWidth : ℝ
  mesh_nonneg : 0≤ mesh
  binWidth_pos : 0< binWidth
  widths_pos : ∀ s∈slots,0< widths s
  widths_mesh : ∀ s∈slots,widths s≤ mesh
  supply : 7/37≤∑ s∈slots,widths s

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

abbrev Batch.Bin (B : Batch M H Label Slot U a ε tstar T allowance i) :=
  BinLabel B.slots ((2*a-1)/2) B.binWidth

def Batch.fiberRows (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U)) : Finset FreeRow :=
  fiber B.rows B.family U a ε tstar T allowance i B.witness B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U) bin j J K

def Batch.fiber (B : Batch M H Label Slot U a ε tstar T allowance i)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : Fiber M H Label Slot U a ε tstar T allowance i :=
  toFiber M H B.rows B.family U a ε tstar T allowance i B.witness B.row_norm B.data B.reverse
    B.row_coeff B.slots B.profile B.upper B.widths B.external B.mesh B.binWidth B.mesh_nonneg
    B.binWidth_pos B.widths_pos B.widths_mesh B.supply bin j J K hne

def Batch.q (B : Batch M H Label Slot U a ε tstar T allowance i) (bin : B.Bin) : ℝ :=
  weightedMean B.slots B.widths (binValue B.slots ((2*a-1)/2) B.binWidth bin)

theorem Batch.card_eq_sum_fibers [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i) :
    B.rows.card=∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows bin j J K).card :=
  HeckeDetectorFiberPartition.card_eq_sum_fibers B.rows B.family U a ε tstar T allowance i B.witness
    B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U)

/-- Summing fiber bounds costs the label count and two dyadic scale counts. -/
theorem Batch.card_bound [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i)
    (C : ℝ) (exponent : B.Bin→ℝ) (hC : 0≤ C) (hU : 0< U)
    (hfiber : ∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
      ((B.fiber bin j J K hne).rows.card : ℝ)≤ C*U^(exponent bin)) :
    (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2*C*
      ∑ bin : B.Bin,U^(exponent bin) := by
  have he : (B.rows.card : ℝ)=∑ bin : B.Bin, ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows bin j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C*U^(exponent bin) := by
      apply Finset.sum_le_sum
      intro bin _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows bin j J K).Nonempty
      · exact hfiber bin j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty,Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←mul_assoc]
      rw [←Finset.mul_sum]
      ring

end HeckeDetectorBatch

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount HeckeDetectorPlainFiberCount HeckeDetectorNoSlotPlainCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.lengths (F : Fiber M H Label Slot U a ε tstar T allowance i) (hU : 1< U) :
    tstar-F.r-ε≤ F.m ∧ F.r≤ tstar+ε ∧ F.m≤1/2+75*ε ∧ tstar-1/2-76*ε≤ F.r ∧ 0≤ F.m :=
  fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hU F.witness
    F.left F.right F.fixed_left F.fixed_right

theorem Fiber.inverse_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1< U) (ha : 1/2≤ a) (hC : 0≤ C) (hh : 0≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (z : ℝ) (hz : 0≤ z) (hz' : z≤7/37) (hcap1 : F.r+2*z<1) (hcap2 : 2*F.r+8*z<3) :
    (F.rows.card : ℝ)≤(12*(1+height)*C)*U^(1-(2*a-1)*F.r-2*F.q*z+2*ε+(2*a-1)*F.mesh+εm) := by
  exact inverse_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin hC hh hf hcap1 hcap2 moments.inverse_marked

theorem Fiber.plain_marked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1< U) (ha : 1/2≤ a) (hΔ : 0≤Δ) (hC : 0≤ C) (hh : 0≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height)
    (z : ℝ) (hz : 0≤ z) (hz' : z≤7/37) (hcap : 2*F.m+6*(3/4+2*Δ)*z≤1) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(1-2*(2*a-1)*F.m-2*F.q*z+4*ε+(2*a-1)*F.mesh+εm) := by
  exact plain_fiber_count M H F.rows F.nonempty F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    F.slots (fun u => u.val) F.profile F.upper F.widths F.bin F.external F.mesh F.binWidth z (3/4+2*Δ) εm C height
    F.mesh_nonneg F.binWidth_pos F.widths_pos F.widths_mesh (by linarith [F.supply])
    hz (hz'.trans F.supply) F.fixed_bin (by linarith) hC hh hf hcap moments.plain_marked

theorem Fiber.plain_unmarked_count (F : Fiber M H Label Slot U a ε tstar T allowance i)
    {Δ c κ C height εm : ℝ} (moments : Moments F Δ c κ C height εm)
    (hU : 1< U) (ha : 0≤ a) (hC : 0≤ C) (hh : 0≤ height)
    (hf : 2*Real.pi*allowance+(3*i : ℕ)*T≤ height) :
    (F.rows.card : ℝ)≤(192*(1+height)*C)*U^(max 1 (2*F.m)-2*(2*a-1)*F.m+4*ε+εm) := by
  exact no_slot_plain_count F.rows F.family U a ε tstar T allowance i hU ha
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    εm C height hC hh hf moments.plain_unmarked

def fiberConstant (C height K : ℝ) : ℝ := (192*(1+height)*C)*max 1 K

theorem fiberConstant_bounds (C height K : ℝ) (hC : 0≤ C) (hh : 0≤ height) (hK : 0≤ K) :
    0≤ fiberConstant C height K ∧ 192*(1+height)*C≤ fiberConstant C height K ∧
      12*(1+height)*C≤ fiberConstant C height K ∧
      12*(1+height)*(C*K)≤ fiberConstant C height K := by
  have h1 : 0≤192*(1+height)*C := by positivity
  have h2 : 12*(1+height)*C≤192*(1+height)*C := by nlinarith
  have hbig : 192*(1+height)*C≤ fiberConstant C height K :=
    le_mul_of_one_le_right h1 (le_max_left _ _)
  refine ⟨h1.trans hbig,hbig,h2.trans hbig,?_⟩
  calc
    _ = (12*(1+height)*C)*K := by ring
    _ ≤ (192*(1+height)*C)*max 1 K := mul_le_mul h2 (le_max_right _ _) hK h1

end HeckeDetectorRawFiber

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace HeckeDetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤ tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(max (shortExponent (2*a-1) (F.q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+F.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot F moments
  let δ := 2*a-1
  let x := F.q/δ
  have hδ : 0<δ := by dsimp [δ]; linarith
  have ha' : 1/2≤ a := by linarith
  have hδ1 : δ≤1 := by dsimp [δ]; linarith
  obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
  have hx : 0≤ x := div_nonneg hq0 hδ.le
  have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ*x=F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  have hUp : 0< U := zero_lt_one.trans hU
  obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C'≤ fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ)≤ C'*U^p) (hpq : p≤ q) :
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*U^q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hI0 : (F.rows.card : ℝ)≤ fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ)≤ fiberConstant C height K₀*
      U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23/37≤ F.r → F.r<1 → ν<(1-F.r)/2 →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(inverseExponent δ x F.r+commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  have hP : F.r≤ crossing x tstar → F.m<1/2 → ν<(1-2*F.m)/(9/2+12*Δ) →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*
        U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(9/2+12*Δ)+commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hz,hz',hcap⟩ := plain_requested_capacity Δ x tstar F.r F.m ε ν hΔ hx hx' ht ht'
      hr hgeom.1 (by linarith) hν.le hv
    have hb := F.plain_marked_count moments hU ha' hΔ hC hh hf
      ((1-2*F.m)/(9/2+12*Δ)-ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss F.m δ x Δ ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx] using hl
  have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x Δ
    tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap hx hx' hΔ hΔ'
    ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert hc' using 1; congr 2
  unfold commonLoss
  ring

end HeckeDetectorCountFromMoments

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace HeckeDetectorBatchCount
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows HeckeDetectorRowCount

theorem batch_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤ tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2* fiberConstant C height K₀*
        ∑ bin : B.Bin,U^(max (shortExponent (2*a-1) (B.q bin/(2*a-1)) tstar)
          (longExponent (2*a-1) tstar)+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot _ B moments
  apply B.card_bound (fiberConstant C height K₀) _
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU)
  intro bin j J K hne
  exact hcount a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    (B.fiber bin j J K hne) (moments bin j J K hne)

end HeckeDetectorBatchCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace HeckeDetectorHighCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1< U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε (3/2) T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤ fiberConstant C height K₀*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε T allowance Δ C height i hU ha ha' hε hεsmall hC hh hf Label Slot F moments
  have hgeom := F.lengths hU
  have hr0 : 0≤ F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  obtain ⟨hconst,_,_,hconstI⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have hi := hamp F.rows F.family a ε (3/2) T allowance i hU (by linarith)
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hb : (F.rows.card : ℝ)≤ fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+(2*ε+εm)) := by
    apply hi.trans
    convert mul_le_mul_of_nonneg_right hconstI
      (Real.rpow_nonneg (zero_lt_one.trans hU).le
        (max 1 ((1+5*F.r)/6)-(2*a-1)*F.r+2*ε+εm)) using 1 <;> congr 2; ring
  have hout := high_bin_count hconst hU.le ha (show 2*a-1≤1 by linarith)
    (show 0≤76*ε by positivity) (show 1-76*ε≤ F.r by linarith [hgeom.2.2.2.1]) hb
  convert hout using 1; congr 2; ring

end HeckeDetectorHighCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace HeckeDetectorAmplitudeFirst
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorFiberPartition
open HeckeDetectorPhysicalSelection HeckeDetectorAdaptiveCutoff

def amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) : Finset Row :=
  rows.filter (fun u => amplitudeLabel slots U cap mesh hm widths physical u=bin)

def rowMean {Row Slot : Type*} (slots : Finset Slot) (U cap mesh : ℝ)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ) (u : Row) : ℝ :=
  weightedMean slots widths (fun s => HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s))

def classMean {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (widths : Slot→ℝ) (bin : BinLabel slots cap mesh) : ℝ :=
  weightedMean slots widths (binValue slots cap mesh bin)

theorem rowMean_eq {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots cap mesh) (u : Row)
    (hu : u∈amplitudeRows rows slots U cap mesh hm widths physical bin) :
    rowMean slots U cap mesh widths physical u=classMean slots cap mesh widths bin := by
  have he := (Finset.mem_filter.mp hu).2
  unfold rowMean classMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  have hv := congrArg (fun f : BinLabel slots cap mesh => (f ⟨s,hs⟩).val) he
  have hval : HeckePrimeAmplitudeBins.amplitude (U^(widths s)) cap mesh (physical u s)=
      binValue slots cap mesh bin s := by
    simpa only [amplitudeLabel,binValue,dif_pos hs] using hv
  exact congrArg (fun x => widths s*x) hval

theorem classMean_bounds {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U δ mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (bin : BinLabel slots (δ/2) mesh) (hδ : 0≤δ)
    (hw : ∀ s∈slots,0≤ widths s) (hsupply : 0<∑ s∈slots,widths s)
    (hne : (amplitudeRows rows slots U (δ/2) mesh hm widths physical bin).Nonempty) :
    0≤ classMean slots (δ/2) mesh widths bin ∧ classMean slots (δ/2) mesh widths bin≤δ/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←rowMean_eq rows slots U (δ/2) mesh hm widths physical bin u hu]
  apply weightedMean_bounds slots widths _ δ hw hsupply
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

def recut {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    SupportedWitness χ U a ε t' T allowance i := he ▸ w

theorem recut_values {Label : Type*} {χ : Label→Character} {U a ε t t' T allowance : ℝ} {i : ℕ}
    (w : SupportedWitness χ U a ε t T allowance i) (he : t=t') :
    (recut w he).label=w.label ∧ (recut w he).zero=w.zero ∧
    (recut w he).left=w.left ∧ (recut w he).right=w.right ∧
    (recut w he).nu=w.nu ∧ (recut w he).r=w.r ∧ (recut w he).m=w.m := by
  cases he
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def classWitness {Row Label Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (χ : Row→Label→Character) (U a ε T allowance mesh : ℝ) (i : ℕ) (hm : 0< mesh)
    (widths : Slot→ℝ) (physical : Row→Slot→ℂ)
    (w : ∀ u : rows,SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (rowMean slots U ((2*a-1)/2) mesh widths physical u)) T allowance i)
    (bin : BinLabel slots ((2*a-1)/2) mesh)
    (u : amplitudeRows rows slots U ((2*a-1)/2) mesh hm widths physical bin) :
    SupportedWitness (χ u) U a ε
      (cutoff (2*a-1) (classMean slots ((2*a-1)/2) mesh widths bin)) T allowance i :=
  recut (w ⟨u.val,(Finset.mem_filter.mp u.property).1⟩)
    (congrArg (cutoff (2*a-1))
      (rowMean_eq rows slots U ((2*a-1)/2) mesh hm widths physical bin u.val u.property))

theorem card_eq_sum_amplitudeRows {Row Slot : Type*} (rows : Finset Row) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ) (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots cap mesh,(amplitudeRows rows slots U cap mesh hm widths physical bin).card := by
  exact Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=amplitudeLabel slots U cap mesh hm widths physical) (by intro u hu; exact Finset.mem_univ _)

end HeckeDetectorAmplitudeFirst

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter
namespace HeckeDetectorClassBudget
open HeckeDetectorFiberPartition HeckeDetectorWitnessRows

def alphabetBound (mesh : ℝ) : ℕ := 2+(⌈(1/2 : ℝ)/mesh⌉+1 : ℤ).toNat

theorem labels_card_le (cap mesh : ℝ) (hcap : cap≤1/2) (hm : 0< mesh) :
    (HeckePrimeAmplitudeBins.labels cap mesh).card≤ alphabetBound mesh := by
  have hceil : ⌈cap/mesh⌉≤⌈(1/2 : ℝ)/mesh⌉ :=
    Int.ceil_mono (div_le_div_of_nonneg_right hcap hm.le)
  have hsub : Finset.Icc (0 : ℤ) ⌈cap/mesh⌉ ⊆ Finset.Icc (0 : ℤ) ⌈(1/2 : ℝ)/mesh⌉ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2.trans hceil⟩
  have h1 := Finset.card_insert_le (0 : ℝ)
    (insert cap ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ))))
  have h2 := Finset.card_insert_le cap
    ((Finset.Icc (0 : ℤ) ⌈cap/mesh⌉).image (fun n : ℤ => mesh*(n : ℝ)))
  have h3 := Finset.card_image_le (s:=Finset.Icc (0 : ℤ) ⌈cap/mesh⌉)
    (f:=fun n : ℤ => mesh*(n : ℝ))
  have h4 := Finset.card_le_card hsub
  simp only [Int.card_Icc,sub_zero] at h4 h3
  unfold HeckePrimeAmplitudeBins.labels alphabetBound
  omega

theorem bin_card_le {Slot : Type*} (slots : Finset Slot) (cap mesh : ℝ)
    (hcap : cap≤1/2) (hm : 0< mesh) :
    Fintype.card (BinLabel slots cap mesh)≤(alphabetBound mesh)^slots.card := by
  simpa only [BinLabel,Fintype.card_fun,Fintype.card_coe] using
    Nat.pow_le_pow_left (labels_card_le cap mesh hcap hm) slots.card

theorem dyadic_cost_eventually (η : ℝ) (hη : 0<η) :
    ∃ K : ℝ,0≤ K ∧ ∀ᶠ U : ℝ in atTop,(dyadicLength U : ℝ)^2≤ K*U^η := by
  let K := 625/(Real.log 2)^2
  have hK : 0≤ K := by positivity
  have hlog := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hη).bound (by norm_num : (0 : ℝ)<1)
  refine ⟨K,hK,?_⟩
  filter_upwards [hlog,eventually_ge_atTop (2 : ℝ)] with U hlog hU
  have hUp : 0< U := by linarith
  have hs : (Real.log U)^2≤ U^η := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (Real.log U)),
      abs_of_nonneg (Real.rpow_nonneg hUp.le _),one_mul] using hlog
  have hd := HeckeDetectorBudget.source_pair_count_bound U hU
  calc
    (dyadicLength U : ℝ)^2 ≤ 625*(Real.logb 2 U)^2 := hd
    _ = K*(Real.log U)^2 := by unfold K Real.logb; ring
    _ ≤ K*U^η := mul_le_mul_of_nonneg_left hs hK

end HeckeDetectorClassBudget

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace HeckeDetectorFixedAmplitudeCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

lemma fiber_mean_eq (B : Batch M H Label Slot U a ε tstar T allowance i) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : (B.fiber bin j J K hne).q=q := by
  let u := hne.choose
  have hu : u ∈ B.fiberRows bin j J K := hne.choose_spec
  have huR : u∈B.rows := (Finset.mem_filter.mp hu).1
  rw [←hq u huR]
  unfold Fiber.q rowMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun g=> B.widths s*g) ((B.fiber bin j J K hne).fixed_bin u hu s hs).symm

lemma batch_mean_bounds (B : Batch M H Label Slot U a ε tstar T allowance i)
    (hne : B.rows.Nonempty) (ha : 1/2≤ a) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) :
    0≤ q ∧ q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←hq u hu]
  apply weightedMean_bounds B.slots B.widths _ (2*a-1)
    (fun s hs=>(B.widths_pos s hs).le) (by linarith [B.supply])
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

theorem fixed_amplitude_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε tstar T allowance Δ ν C height q : ℝ) (i : ℕ),
      1< U → 51/100< a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤ tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤ height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height q i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf Label Slot _ B hq moments
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _=> max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
      Δ/4+159*ε+εm+B.mesh+7*ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount a ε tstar T allowance Δ ν C height i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne)
      rw [fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc')
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end HeckeDetectorFixedAmplitudeCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace HeckeDetectorHighBatchCount
open HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorRowCount

theorem high_batch_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0≤ K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height : ℝ) (i : ℕ),
      1< U → 5/6≤2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤ C → 0≤ height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤ height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (3/2) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorHighCount.high_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf Label Slot _ B moments
  have hb := B.card_bound (fiberConstant C height K₀) (fun _=>1-(2*a-1)+78*ε+εm)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      exact hcount a ε T allowance Δ C height i hU ha ha' hε hε' hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne))
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end HeckeDetectorHighBatchCount

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

namespace EisensteinLatticeCount
/-- The integral norm-ball count also bounds balls with a real radius. -/
theorem finite_element_count_real (S : Finset Eisenstein.O) (H : ℝ) (hH : 1≤ H)
    (hN : ∀x∈S, ‖ringComplex x‖^2≤ H) :
    (S.card : ℝ)≤128*H := by
  have hc := finite_norm_ball_card S ⌊H⌋₊ (by
    intro x hx
    rw [ringComplex_norm_sq_eq_absNorm_span]
    have hn : (Ideal.absNorm (Ideal.span {x}) : ℝ)≤ H := by
      simpa only [ringComplex_norm_sq_eq_absNorm_span] using hN x hx
    exact_mod_cast Nat.le_floor hn)
  have hf : (⌊H⌋₊ : ℝ)≤ H := Nat.floor_le (by linarith only [hH])
  have hr : (S.card : ℝ)≤64*((⌊H⌋₊ : ℝ)+1) := by exact_mod_cast hc
  linarith only [hr,hf,hH]
end EisensteinLatticeCount

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
