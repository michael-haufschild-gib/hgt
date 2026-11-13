/-
Adaptive source counts adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeRows.CentralCubeRows

/-!
# Adaptive source counts

Source moment data and adaptive row exponents; source dyad conductors and reverse moments; the
adaptive source count from raw moments and canonical dyad costs.
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
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem balanced_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) :
    ∃c κ K : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤ n → 51/100< a → 2*a-1≤5/6 → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤ C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤ N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK₀,hcount⟩ := balanced_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem high_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) :
    ∃c κ K : ℝ,0< c ∧ c≤1 ∧ 0<κ ∧ 0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε Δ C q : ℝ) (i : ℕ),i≤ n → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤ C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤ N → B.binWidth=binWidth →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK₀,hcount⟩ := high_adaptive_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨c,κ,K,hc,hc1,hκ,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha ha' hε hε' (by positivity)
    (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

/-- The balanced or high-zero count exponent selected by the detector range. -/
def adaptiveRowExponent (δ q Δ ε εm slotMesh ν : ℝ) : ℝ :=
  if δ≤5/6 then Endpoint.balancedRowCount δ (1/2-q/δ)+Δ/4+159*ε+εm+slotMesh+7*ν
  else 1-δ+78*ε+εm

theorem adaptive_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤ H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type*) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0< dmin) (hdmax : 0< dmax) (hτ : 0<τ)
    (hl : 0< logCost) (hh : τ< heightCost) (hb : 0< binWidth) :
    ∃cB κB cH κH K : ℝ,0< cB ∧ cB≤1 ∧ 0<κB ∧ 0< cH ∧ cH≤1 ∧ 0<κH ∧ 0< K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤ n → 51/100< a → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤ C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤ N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=> u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤ K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  obtain ⟨cB,κB,KB,hcB,hcB1,hκB,hKB,hbalanced⟩ := balanced_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb
  obtain ⟨cH,κH,KH,hcH,hcH1,hκH,hKH,hhigh⟩ := high_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb
  refine ⟨cB,κB,cH,κH,max KB KH,hcB,hcB1,hκB,hcH,hcH1,hκH,lt_of_lt_of_le hKB (le_max_left _ _),?_⟩
  filter_upwards [hbalanced,hhigh,eventually_ge_atTop (1:ℝ)] with Z hb hh hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2*a-1≤5/6
  · simp only [if_pos hδ] at hmom
    have hc := hb d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    simp only [adaptiveRowExponent,if_pos hδ]
    exact hc.trans (by gcongr;exact le_max_left _ _)
  · simp only [if_neg hδ] at hmom
    have hc := hh d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    simp only [adaptiveRowExponent,if_neg hδ]
    exact hc.trans (by gcongr;exact le_max_right _ _)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma dyadic_weighted_rows_card (α r C U B : ℝ) (hC : 0≤ C) (hU : 0< U)
    (R : Finset FreeRow) (hcard : (R.card:ℝ)≤ B)
    (hR : ∀u∈R,U≤ rowNorm u ∧ rowNorm u≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤ C*rowNorm u^α)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      B*C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (α-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0< rowNorm u := hU.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      change rowNorm u^(-r)*F u≤ _
      calc
        _ ≤ rowNorm u^(-r)*(C*rowNorm u^α) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*rowNorm u^(α-r) := by
          rw [show α-r=(-r)+α by ring,Real.rpow_add hN]; ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U (rowNorm u) (α-r)
            (by norm_num) (by norm_num) hU (by simpa using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) := by simp
    _ ≤ B*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

lemma annular_power_uniform (p pmax : ℝ) (hp : p≤ pmax) :
    ProbeSelectedPrimeSums.annularPower 1 2 p≤ max 1 ((2:ℝ)^pmax) := by
  unfold ProbeSelectedPrimeSums.annularPower
  rw [Real.one_rpow]
  exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp)

/-- The source exponent with the conductor and row-norm scales separated. -/
def mixedSourceExponent (a v d R q : ℝ) : ℝ :=
  ProbeCentralExponent.sourceExponent a v R q+(d-v)*R

lemma mixed_physical_exponent (Z a v d R q e eps loss mesh : ℝ) (N : ℕ)
    (hZ : 0< Z) :
    ((Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e))*
      ((Z^d)^R*(Z^v)^(a-1/2+12*e+eps*(N+8)-17/50)*Z^(-2/75+q/6+mesh/6+loss))=
    Z^(mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

lemma mixed_source_slack (a v d R q μ Rmax : ℝ)
    (hR : 0≤ R) (hRmax : R≤ Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedSourceExponent a v d R q≤ ProbeCentralExponent.sourceExponent a v R q+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedSourceExponent
  linarith

lemma dyad_conductor_margin (Z v margin : ℝ) (hZ : 0< Z) (hmargin : 2≤ Z^margin)
    (R : Finset FreeRow) (hR : ∀u∈R,rowNorm u≤2*Z^v) :
    ∀u∈R,rowNorm u≤ Z^((v+2*margin)-margin) := by
  intro u hu
  calc
    rowNorm u≤2*Z^v := hR u hu
    _ ≤ Z^margin*Z^v := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeHighRowFamily
open HeckeDetectorRowCount ProbeCentralExponent

lemma balanced_count_range (δ x Δ loss : ℝ) (hδ : 0≤δ) (hd : δ≤5/6)
    (hx : 0≤ x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (hl : 0≤ loss) (hl' : loss≤1/32) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    1-δ≤ R ∧ R≤3/2 := by
  have ht := balanced_cutoff_bounds hδ hd hx hx'
  have hp0 := mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤ Endpoint.balancedCutoff δ (1/2-x)-1 by linarith)
  have hp1 := mul_le_mul_of_nonneg_left ht.2 (show 0≤5/6-δ by linarith)
  dsimp only
  unfold Endpoint.balancedRowCount
  constructor <;> nlinarith

lemma balanced_mixed_margin (δ x Δ loss ζ μ v d : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤ x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤ loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    mixedSourceExponent ((1+δ)/2) v d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ+(3/2)*μ := by
  dsimp only
  let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
  have hr := balanced_count_range δ x Δ loss hδ hd hx hx' hΔ hΔ' hl hl'
  have hlo : 0≤ R+δ/2-17/50 := by dsimp [R]; linarith [hr.1]
  have hhi : R+δ/2-17/50≤2 := by dsimp [R]; linarith [hr.2]
  have hm := balanced_source_margin δ x R Δ loss ζ v hδ hd hx hx' le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d R (δ*x) μ (3/2)
    (by dsimp [R];linarith [hr.1]) hr.2 hμ hdv
  linarith

lemma high_mixed_margin (δ q Δ loss ζ μ v d : ℝ)
    (hδ : 5/6≤δ) (hd : δ≤1) (hq : q≤δ/2)
    (hl : 0≤ loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    mixedSourceExponent ((1+δ)/2) v d (1-δ+loss) q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ+μ := by
  have hlo : 0≤(1-δ+loss)+δ/2-17/50 := by linarith
  have hhi : (1-δ+loss)+δ/2-17/50≤2 := by linarith
  have hm := high_source_margin δ (1-δ+loss) q Δ loss ζ v hq le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d (1-δ+loss) q μ 1
    (by linarith) (by linarith) hμ hdv
  linarith

lemma balanced_mixed_saving (δ x Δ loss ζ μ v d other saving : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤ x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤ loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : (13/16)*loss+2*ζ+(3/2)*μ+other+saving≤49/440640) :
    mixedSourceExponent ((1+δ)/2) v d
      (Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss) (δ*x)+other≤3/16+Δ-saving := by
  have hm := balanced_mixed_margin δ x Δ loss ζ μ v d hδ hd hx hx' hΔ hΔ' hl hl' hζ hv hμ hdv
  linarith
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbeHighRowFamily

lemma adaptive_mixed_saving (N : ℕ) (a q Δ ε εm slotMesh ν ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1/2< a) (ha' : a≤1) (hq : 0≤ q) (hq' : q≤(2*a-1)/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hε : 0≤ε) (hεm : 0≤εm)
    (hslot : 0≤ slotMesh) (hν : 0≤ν)
    (hcount : 159*ε+εm+slotMesh+7*ν≤1/32)
    (hζ : 0≤ζ) (hζ' : ζ≤3/16) (hv : v≤13/16+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ) (he : 0≤ e) (heps : 0≤ eps)
    (hbudget : (13/16)*(159*ε+εm+slotMesh+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+overhead+saving≤49/440640) :
    mixedSourceExponent a v d (adaptiveRowExponent (2*a-1) q Δ ε εm slotMesh ν) q+
      ProbeCentralExponent.realLoss N v e eps loss mesh+overhead≤3/16+Δ-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hx : 0≤ q/(2*a-1) := div_nonneg hq hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0≤159*ε+εm+slotMesh+7*ν := by positivity
  have haeq : (1+(2*a-1))/2=a := by ring
  have hqeq : (2*a-1)*(q/(2*a-1))=q := mul_div_cancel₀ q hδ.ne'
  have hr := ProbeCentralExponent.realLoss_bound N v e eps loss mesh (by linarith) he heps
  by_cases hd : 2*a-1≤5/6
  · have hb := balanced_mixed_saving (2*a-1) (q/(2*a-1)) Δ (159*ε+εm+slotMesh+7*ν)
      ζ μ v d (ProbeCentralExponent.realLoss N v e eps loss mesh+overhead) saving
      hδ.le hd hx hx' hΔ hΔ' hl hcount hζ hv hμ hdv (by linarith)
    rw [haeq,hqeq] at hb
    simpa only [adaptiveRowExponent,if_pos hd,add_assoc] using hb
  · have hhl : 0≤78*ε+εm := by positivity
    have hh := high_mixed_margin (2*a-1) q Δ (78*ε+εm) ζ μ v d
      (le_of_lt (lt_of_not_ge hd)) (by linarith) hq' hhl (by linarith)
      hζ hv hμ hdv
    rw [haeq] at hh
    simp only [adaptiveRowExponent,if_neg hd]
    simp only [add_assoc] at hh ⊢
    linarith

lemma central_class_exponent_identity (N : ℕ) (a v d R q e eps loss mesh overhead : ℝ) :
    ((25/48)*a-181/300+(105/8)*e)+
      (overhead+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6)=
    mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh+overhead := by
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The ray-amplitude bins hold uniformly on the central height cube. -/
theorem actual_phase_bins_on_cube (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (hmax : ∀P∈S,P.IsMaximal)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0< A) (hAB : A≤ B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh δ ν : ℝ) (n : ℕ)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0< e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hν : 0<ν) (hheight : 2*τ< dmin*cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax → 2≤ Z^d → 2< Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤ rowNorm u →
      (ProbePhysical.calibrationForSet S hmax).residueMonoid u.val≠0 →
      rowNorm u≤ Z^(d-ν) →
    ∀(a : ℝ) (i : ℕ),i≤ n → 51/100≤ a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)< a+2*e →
    ∀(r : ℝ) (t : ProbeMellinBoundary.HeightSpace),rmin≤ r → r≤ R →
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
    let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤ g ∧ g≤ a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤ D^(g+mesh) ∧ (0< g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤ D^(z.re-1/2+g+mesh) := by
  have hb := ProbeRayPhaseBins.actual_phase_bins M H hH S hS hbad W A B hA hAB hWs hW
    R dmin dmax rmin τ ε e κ cost mesh (33/50) (33/50) δ
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hδ hbudget hgap
  filter_upwards [hb,cube_height_budget_eventually n τ dmin cost hτ hcost hheight,
    ray_cube_conductor_eventually M ν hν,eventually_gt_atTop (0:ℝ)] with Z hb hh hc hZ
  intro d hd hd' hU hT η u hu hcal hrow a i hi ha ha' hbin r t hr hr' ht
  have hs := calibration_nonzero_supported S hmax hbad u.val hcal
  have hpow : 0≤ Z^τ := Real.rpow_nonneg hZ.le _
  have hbuffer : ((3*i+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*i+2:ℕ)*Z^τ := by
    push_cast
    nlinarith
  have hfreq := (cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht hpow hbuffer).2.2
  have hb' := hb d hd hd' hU hT η u hu hs (hc u d hrow) a i ha ha' hbin r
    ((17/50:ℂ)+t.1.2*Complex.I) hr hr'
    (by norm_num) (by norm_num) (by simpa using hfreq) (hh i hi d hd)
  exact hb'

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter
namespace ProbeHighRowFamily
open HeckeFamily ProbeRaySlots
local notation "O" => Eisenstein.O

/-- Primes in growing ray pools eventually avoid the conductor and satisfy the local correction bounds. -/
theorem central_pool_good_eventually (η : Character) (e c b dmin rmin : ℝ)
    (he : 0< e) (hc : 0< c) (hcb : c≤ b) (hd : 0< dmin) (hr : 0< rmin) :
    ∀ᶠ Z : ℝ in atTop,∀(C : Set (Ideal O)) (S : Finset (Ideal O)) (d r : ℝ),dmin≤ d → rmin≤ r →
      ∀P∈pool C S c b ((Z^d)^r),P.val∉S ∧ IsCoprime P.val η.modulus ∧
        (480:ℝ)≤ P.val.absNorm ∧ 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2 := by
  obtain ⟨Q0,hQ0,hsmall⟩ := ProbeEuler.central_correction_threshold e he
  have ht := (tendsto_rpow_atTop (mul_pos hd hr)).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop Q0),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ))] with Z hZ hQ hη
  intro C S d r hdd hrr P hP
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hle : c*Z^(dmin*rmin)≤ c*(Z^d)^r := by
    rw [←Real.rpow_mul hZp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul hdd hrr hr.le (hd.trans_le hdd).le)) hc.le
  have hl := (pool_norm_bounds C S hc.le hcb hD P hP).1
  have hq : Q0≤(P.val.absNorm:ℝ) := hQ.trans (hle.trans (by linarith))
  exact ⟨(mem_pool C S c b _ P).mp hP |>.2.2.2,
    prime_coprime_of_norm_gt η P (hη.trans_le (hle.trans (by linarith))),hQ0.trans hq,hsmall _ hq⟩

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=1/6) :
    (∑j∈slots,ell j/d)=1/(6*d) := by
  rw [←Finset.sum_div,hell]
  ring

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    weightedMean slots (fun j=> ell j/d) g=6*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

/-- Slot lengths summing to one sixth turn the prime product into a weighted-mean exponent. -/
lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0< Z) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(2/75:ℝ)+weightedMean slots (fun j=> ell j/d) g/6+mesh/6) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  ring

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤ Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

/-- The frequency weights reduce the arithmetic sum to a weighted row mass. -/
lemma cubeArithmeticSum_norm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→ Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀j P,P∈T j→ P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace)
    (A : FreeRow→ℝ)
    (hA : ∀u∈R,‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=> hT j _ (P j).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)‖≤ A u) :
    ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤
      ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u := by
  unfold cubeArithmeticSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu=>?_)
  rw [norm_mul,frequencyWeight_ideal_norm]
  have hz : (((17/50:ℂ)+t.1.2*Complex.I).re:ℝ)=17/50 := by simp
  rw [hz]
  exact mul_le_mul_of_nonneg_left (hA u hu) (Real.rpow_nonneg (by positivity) _)

/-- A common Mellin profile bounds the cube integral by its row mass. -/
theorem actual_common_cube_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0< e → e<1/1000 → 51/100≤ a → a≤1 → 2< B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→ Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀j P,P∈T j→ P.val∉S)
      (ψ : FreeRow→ι→ Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)< a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0< X → 0< Y → 0< Z →
    ∀A : FreeRow→ℝ,(∀u∈R,0≤ A u) →
      (∀t : HeightSpace,(|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H → ∀u∈R,
        ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=> hT j _ (P j).property) W Yp
          (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
          ((17/50:ℂ)+t.1.2*Complex.I)‖≤ A u) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=> a) (fun _=> H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          (∑u∈R,rowNorm u^(-(17/50:ℝ))*A u) := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H}
  let V : HeightSpace→ℂ := fun t=> sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=> V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u
  have hm : 0≤ mass := Finset.sum_nonneg fun u hu=> mul_nonneg (Real.rpow_nonneg (by unfold rowNorm;positivity) _) (hA u hu)
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤ scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=> scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤ scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (cubeArithmeticSum_norm S hS hmax η R T hT W Yp a e t A (hb t ht)) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring

/-- A uniform arithmetic bound controls the common-profile cube integral. -/
theorem actual_common_cube_aggregate_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0< C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0< e → e<1/1000 → 51/100≤ a → a≤1 → 2< B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→ Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀j P,P∈T j→ P.val∉S)
      (ψ : FreeRow→ι→ Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)< a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0< X → 0< Y → 0< Z →
    ∀A : ℝ,0≤ A →
      (∀t : HeightSpace,(|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H →
        ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤ A) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=> a) (fun _=> H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          A := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤ H ∧ |t.2|≤ H) ∧ |t.1.2|≤ H}
  let V : HeightSpace→ℂ := fun t=> sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=> V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := A
  have hm : 0≤ mass := hA
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤ scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=> scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤ scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure CanonicalRowCompletion
open ProbePhysical

def momentData (η : Character) : RowData where
  η := η
  m := rowMaskElement
  f := 1
  m_ne_zero := rowMaskElement_ne_zero
  f_ne_zero := one_ne_zero
  lambda_dvd := dvd_mul_left _ _
  two_dvd := dvd_mul_right _ _

def momentElement (u : FreeRow) : NonzeroElement := ⟨u.val,u.property.1⟩

/-- The moment character has the required masked sextic coefficients. -/
theorem momentData_coeff (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData η).character (momentElement u)) I=
      idealCoeff η I*idealRowHom (rowMaskElement^6*u.val) I := by
  simpa only [momentData,momentElement,one_pow,mul_one] using
    idealCoeff_eq_row η ((momentData η).character (momentElement u)) rowMaskElement 1 u.val
      ((momentData η).character_spec (momentElement u)) I

theorem momentData_prime_outside (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (P : HeckeIdealSeries.PrimeIdeal) (hP : P.val∉S) :
    idealCoeff ((momentData η).character (momentElement u)) P.val=
      idealCoeff η P.val*idealRowHom u.val P.val := by
  let : P.val.IsMaximal := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  obtain ⟨hg,hc⟩ := outside_good_coprime S hS hbad P hP
  rw [momentData_coeff,idealRowHom_argument_mul,
    idealRowHom_prime_sixth_mask rowMaskElement P.val hg,if_pos hc,one_mul]

theorem numerator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (u : FreeRow) (I : Ideal O) :
    idealCoeff (rowCharacter S hS u) I=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) I := by
  have he : idealCoeff (rowCharacter S hS u)=
      idealCoeff ((momentData (fixedSourcePrincipal S hS)).character (momentElement u)) := by
    apply hom_eq_of_primes
    intro P
    change idealCoeff ((rawRow u).excludePrimes S hS) P.val=_
    rw [excludedTarget_prime]
    by_cases hP : P.val∈S
    · rw [if_pos hP,momentData_coeff,fixedSourcePrincipal_prime,if_pos hP,zero_mul]
    · rw [if_neg hP,rawRow_prime_outside S hS hbad u P hP,
        momentData_prime_outside S hS hbad _ u P hP,
        fixedSourcePrincipal_prime,if_neg hP,one_mul]
  exact congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem denominator_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((targetRow η u).excludePrimes S hS) I=
      conj (idealCoeff ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) I) := by
  have he : idealCoeff ((targetRow η u).excludePrimes S hS)=
      idealCoeff (((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)).inverse) := by
    apply hom_eq_of_primes
    intro P
    rw [idealCoeff_inverse_conj]
    change idealCoeff ((η.product (rawRow u).inverse).excludePrimes S hS) P.val=_
    rw [target_inverseRow_coeff S hS hbad]
    by_cases hP : P.val∈S
    · rw [if_pos hP,momentData_coeff,excludedTarget_prime,if_pos hP,zero_mul,map_zero]
    · rw [if_neg hP,momentData_prime_outside S hS hbad _ u P hP,
        excludedTarget_prime,if_neg hP,idealCoeff_inverse_conj,map_mul]
      simp only [starRingEnd_self_apply]
  simpa only [idealCoeff_inverse_conj] using congrArg (fun F : Ideal O→*₀ℂ => F I) he

theorem numerator_moment_polynomial (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    HeckeDyadic.polynomial (rowCharacter S hS u) inv W D σ freq=
      HeckeDyadic.polynomial ((momentData (fixedSourcePrincipal S hS)).character
        (momentElement u)) inv W D σ freq :=
  HeckeDetectorCoefficientTransfer.polynomial_eq_of_idealCoeff _ _
    (numerator_moment_coeff S hS hbad u) inv W D σ freq

theorem denominator_moment_norm (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character) (u : FreeRow)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0< D) :
    ‖HeckeDyadic.polynomial ((targetRow η u).excludePrimes S hS) inv W D σ freq‖=
      ‖HeckeDyadic.polynomial ((momentData (η.inverse.excludePrimes S hS)).character
        (momentElement u)) inv (fun x=> conj (W x)) D σ (-freq)‖ :=
  HeckeDetectorCoefficientTransfer.norm_of_oriented_coefficients _ _ true
    (denominator_moment_coeff S hS hbad η u) inv W D σ freq hD

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter UniqueFactorizationMonoid
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical _root_.GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => Eisenstein.O

def targetPrincipalSupport (η : Character) : Finset (Ideal O) :=
  (normalizedFactors (η.modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)})).toFinset

lemma targetPrincipalSupport_prime (η : Character) : ∀P∈targetPrincipalSupport η,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_target_elementCoeff (η : Character) (u : FreeRow) (n : O) :
    elementCoeff (targetRow η u).inverse n=
      rowTwist (HeckeRowClosure.elementHom ((fixedSourcePrincipal ∅ (by simp)).product η.inverse))
        rowMaskElement 1 u.val n := by
  rw [elementCoeff_inverse]
  unfold targetRow
  rw [elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,rawRow_elementCoeff]
  change (elementCoeff (fixedSourcePrincipal ∅ (by simp)) n *
    idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})) * (elementCoeff η n)⁻¹=
    elementCoeff ((fixedSourcePrincipal ∅ (by simp)).product η.inverse) n *
      idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  ring

theorem principal_target_row_norm_bound (η : Character) (u : FreeRow)
    (hs : Supported (Ideal.span {u.val})) (hp : (targetRow η u).residue=1) :
    rowNorm u≤(HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ) := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val ((supported_iff_native _).mp hs)
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*lambda^0*(2:O)^0*r := by simp [r]
  let η0 := (fixedSourcePrincipal ∅ (by simp)).product η.inverse
  have hmod : η0.modulus=η.modulus := by
    change (1:Ideal O)⊓η.modulus=η.modulus
    simp
  have hinv : (targetRow η u).inverse.residue=1 := by
    change (targetRow η u).residue⁻¹=1
    rw [hp,inv_one]
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η0 (targetRow η u).inverse
    rowMaskElement 1 u.val rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _)
    v⁻¹ 0 0 r hr hv hx (inverse_target_elementCoeff η u) hinv (fun P _=> hspan.symm ▸ u.property.2 P)
  rw [hmod] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (targetPrincipalSupport η) (targetPrincipalSupport_prime η) hfixed
  rw [hspan] at hn
  unfold rowNorm
  exact_mod_cast hn

theorem excluded_target_nonprincipal_eventually (η : Character) (d : ℝ) (hd : 0< d) :
    ∀ᶠ Z : ℝ in atTop,∀u : FreeRow,Z^d≤ rowNorm u →
      Supported (Ideal.span {u.val}) → ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      ((targetRow η u).excludePrimes S hS).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (eventually_gt_atTop (HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ))]
    with Z hZ u hu hs S hS
  intro hp
  have hp' := (HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (targetRow η u) S hS)).mp hp
  exact not_lt_of_ge (principal_target_row_norm_bound η u hs hp') (hZ.trans_le hu)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def sourceConductorConstant (S : Finset (Ideal O)) (η : Character) : ℕ :=
  conductorConstant*(∏P∈S,P).absNorm*(η.modulus.absNorm+1)+conductorConstant*M.absNorm

theorem source_ray_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) :
    (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm≤
      sourceConductorConstant M S η*(Ideal.span {u.val}:Ideal O).absNorm := by
  cases j with
  | inl b =>
    cases b with
    | false =>
      apply (targetRow_excluded_conductor S hS η u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
    | true =>
      apply (rowCharacter_conductor S hS u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
  | inr θ =>
    apply (ProbeRayCharacterFamily.raw_twisted_conductor M H hH u θ).trans
    unfold sourceConductorConstant
    ring_nf
    omega

theorem source_ray_nonprincipal_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (d : ℝ) (hd : 0< d) :
    ∀ᶠ Z : ℝ in atTop,∀U : ℝ,∀u∈rowBand (Z^d) U,
      (calibrationForSet S hmax).residueMonoid u.val≠0 →
      ∀j,(sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue≠1 := by
  filter_upwards [excluded_target_nonprincipal_eventually η d hd,
    ProbeRayCharacterFamily.large_supported_twists_eventually M d hd] with Z htarget hray
  intro U u hu hc j
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hc
  have hnorm := (mem_rowBand.mp hu).2.1
  cases j with
  | inl b =>
    cases b with
    | false => exact htarget u hnorm hs S hS.prime
    | true => exact calibrated_row_nonprincipal S hS.prime hmax hS.bad u (mem_rowBand.mp hu).1 hc
  | inr θ => exact hray u hnorm hs H hH θ

theorem source_ray_maximum_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (d : ℝ) (hd : 0< d) :
    ∀ᶠ Z : ℝ in atTop,∀U : ℝ,∀u∈rowBand (Z^d) U,
      (calibrationForSet S hmax).residueMonoid u.val≠0 →
      ∃hnp : ∀j,(sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue≠1,
      ∀T : ℝ,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) T=
        HeckeDetectorZeros.zeroMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) hnp T := by
  filter_upwards [source_ray_nonprincipal_eventually M H hH S hS hmax η d hd] with Z hZ
  intro U u hu hc
  exact ⟨hZ U u hu hc,fun T=> detectorMaximum_eq_nonprincipal _ _ T⟩

/-- A fixed conductor factor is absorbed by the gap in the row-norm exponent. -/
theorem source_ray_conductor_eventually (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤ Z^(d-ν) →
      ∀j,((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤ Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually (sourceConductorConstant M S η:ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu j
  have hq : ((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤
      (sourceConductorConstant M S η:ℝ)*rowNorm u := by
    unfold rowNorm
    exact_mod_cast source_ray_conductor M H hH S hS η u j
  apply hq.trans
  calc
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology
open Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open HeckeDetectorSupportedWitness
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
variable (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) (η : Character)

/-- The central cube bounds supply supported detector witnesses for every retained row. -/
theorem supported_witnesses_from_source_cube (dmin dmax τ ε e κ heightCost margin : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠ Z : ℝ in atTop,∀ d : ℝ,dmin≤ d → d≤ dmax →
      ∀ (U : ℝ) (rows : Finset FreeRow),rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
      let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
      ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
        (∀u : rows,detectorMaximum (χ u) (3*(i+1 : ℕ)*(Z^τ))< a+2*e) →
        (∀u : rows,a≤ detectorMaximum (χ u) ((3*i : ℕ)*Z^τ)) →
        ∀ tstar : ℝ,1≤ tstar → tstar≤3/2 →
          Nonempty (∀u : rows,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
            ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z0,hdet⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hbudget
  filter_upwards [eventually_ge_atTop Z0,
    source_ray_nonprincipal_eventually M H hH S hS hmax η (1/100) (by norm_num),
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin] with Z hZ hnp hcond
  intro d hd hd' U rows hrows hcal hrow
  dsimp only
  intro a i hi ha ha' hnext hcurrent tstar ht ht'
  let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
  have hχ : ∀u j,(χ u j).residue≠1 := fun u=> hnp U u.val (hrows u.property) (hcal u.val u.property)
  have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hχ u)
  exact hdet Z hZ d hd hd' χ hχ a i hi ha ha'
    (fun u=> by rw [←heq u];exact hnext u)
    (fun u=> by rw [←heq u];exact hcurrent u)
    (fun u=> hcond u.val d (hrow u.val u.property)) tstar ht ht'

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ComplexConjugate
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => Eisenstein.O

theorem momentData_product_raw (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData χ).character (momentElement u)) I=
      idealCoeff (χ.product (rawRow u)) I := by
  have he : idealCoeff ((momentData χ).character (momentElement u))=
      idealCoeff (χ.product (rawRow u)) := by
    apply hom_eq_of_primes
    intro P
    rw [momentData_coeff,idealCoeff_product,rawRow_coeff,fixedSourcePrincipal_prime]
    simp
  exact congrArg (fun f : Ideal O→*₀ℂ=> f I) he

theorem inverse_row_twist_moment_coeff (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((rawRow u).inverse.product χ) I=
      conj (idealCoeff ((momentData χ.inverse).character (momentElement u)) I) := by
  rw [momentData_product_raw,idealCoeff_product,idealCoeff_product,
    idealCoeff_inverse_conj,idealCoeff_inverse_conj,map_mul]
  simp only [starRingEnd_self_apply]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def sourceMomentData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→ RowData :=
  Sum.elim (fun b=> if b then momentData (fixedSourcePrincipal S hS)
    else momentData (η.inverse.excludePrimes S hS))
    (fun θ=> momentData (HeckeRayQuotient.character M H hH θ).inverse)

def sourceMomentReverse : Sum Bool (RayQuotient.Characters M H)→ Bool :=
  Sum.elim (fun b=>!b) (fun _=> true)

/-- Each detector coefficient equals its moment coefficient, with the prescribed conjugation. -/
theorem source_family_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalRowCompletion.fixedBadPrimes⊆S) (η : Character)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    idealCoeff (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) I=
      if sourceMomentReverse M H j then
        conj (idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I)
      else idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I := by
  rcases j with b|θ
  · cases b
    · simpa [sourceMomentReverse,sourceMomentData] using denominator_moment_coeff S hS hbad η u I
    · simpa [sourceMomentReverse,sourceMomentData] using numerator_moment_coeff S hS hbad u I
  · exact inverse_row_twist_moment_coeff (HeckeRayQuotient.character M H hH θ) u I
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorSupportedWitness ProbePhysical
local notation "O" => Eisenstein.O

def retainedProjection (R : Finset FreeRow) (u0 : FreeRow) (u : FreeRow) : FreeRow :=
  if u∈R then u else u0

@[simp] theorem retainedProjection_of_mem (R : Finset FreeRow) (u0 u : FreeRow) (hu : u∈R) :
    retainedProjection R u0 u=u := by simp [retainedProjection,hu]

theorem retainedProjection_mem (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R) (u : FreeRow) :
    retainedProjection R u0 u∈R := by
  unfold retainedProjection
  split_ifs with hu
  · exact hu
  · exact h0

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def retainedSourceBatch {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (hw : ∀u∈R,SupportedWitness
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) U a ε tstar T allowance i)
    (hrow : ∀u∈R,rowNorm u≤ U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hwpos : ∀s∈slots,0< widths s) (hwmesh : ∀s∈slots,widths s≤ mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i where
  rows := R
  family := fun u=> sourceDetectorFamily S hS.prime η (retainedProjection R u0 u)
    (rayCubeFamily M H hH (retainedProjection R u0 u))
  witness := fun u=> hw (retainedProjection R u0 u) (retainedProjection_mem R u0 h0 u)
  row_norm := hrow
  data := sourceMomentData M H hH S hS.prime η
  reverse := sourceMomentReverse M H
  row_coeff := by
    intro u hu j I
    rw [retainedProjection_of_mem R u0 u hu]
    exact source_family_moment_coeff M H hH S hS.prime hS.bad η u j I
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hm
  binWidth_pos := hb
  widths_pos := hwpos
  widths_mesh := hwmesh
  supply := hsupply

lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0< dmin) (hd : dmin≤ d) (hdtop : d≤37/42)
    (hell : ∀j,0< ell j) (hsmall : ∀j,ell j≤ dmin*mesh)
    (hsum : ∑j,ell j=1/6) :
    (∀j,0< ell j/d) ∧ (∀j,ell j/d≤ mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0< d := hdmin.trans_le hd
  have hm : 0≤ mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    norm_num at hn
  refine ⟨fun j=> div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div,hsum]
    apply (le_div_iff₀ hd0).mpr
    nlinarith

lemma physical_slot_scale {N : ℕ} (ell : Fin N→ℝ) (Z d : ℝ) (hZ : 0< Z) (hd : d≠0) (j : Fin N) :
    (Z^d)^(ell j/d)=Z^(ell j) := by
  rw [←Real.rpow_mul hZ.le]
  congr 1
  field_simp
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- The source cube and slot widths give a concrete detector batch. -/
theorem actual_source_batch (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤ tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw,eventually_ge_atTop (1:ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u=> hnext u.val u.property) (fun u=> hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0,h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u∈rows) : rowNorm u≤ Z^d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp,hwm,hsp⟩ := physical_slot_widths ell d dmin mesh hdmin hd (hd'.trans hdtop) hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z^d) a ε tstar (Z^τ)
    ((Z^d)^(τ/(2*dmax))) i (fun u hu=> w ⟨u,hu⟩) hnorm
    Finset.univ W upper (fun j=> ell j/d) z mesh binWidth hm hb (fun j _=> hwp j) (fun j _=> hwm j) hsp
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro u hu j
  dsimp [B,retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Partitioning by amplitude labels gives batches with a constant weighted amplitude. -/
theorem actual_source_amplitude_batches (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
      W upper (fun j=> ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hdtop hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
    W upper (fun j=> ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hcut := HeckeDetectorAdaptiveCutoff.cutoff_bounds (2*a-1) q (by linarith)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=> hcal u (hsub hu)) (fun u hu=> hrow u (hsub hu)) a i hi ha ha'
      (fun u hu=> hnext u (hsub hu)) (fun u hu=> hcurrent u (hsub hu))
      (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=> ell j/d) Q bin u hu'
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

lemma sum_amplitudeRows {Slot : Type*} (rows : Finset FreeRow) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ) (Q : FreeRow→ Slot→ℂ)
    (f : FreeRow→ℂ) :
    (∑u∈rows,f u)=∑bin : BinLabel slots cap mesh,
      ∑u∈amplitudeRows rows slots U cap mesh hm widths Q bin,f u := by
  have hmap : ∀u∈rows,amplitudeLabel slots U cap mesh hm widths Q u∈
      (Finset.univ : Finset (BinLabel slots cap mesh)) := by simp
  exact (Finset.sum_fiberwise_of_maps_to hmap f).symm

/-- The central arithmetic sum splits exactly over amplitude labels. -/
lemma cubeArithmeticSum_amplitude_partition {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→ Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→ P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0< mesh) (widths : Slot→ℝ) (Q : FreeRow→ Slot→ℂ) :
    cubeArithmeticSum S hS hmax η rows T hT W Yp a e t=
      ∑bin : BinLabel slots cap mesh,cubeArithmeticSum S hS hmax η
        (amplitudeRows rows slots U cap mesh hm widths Q bin) T hT W Yp a e t := by
  unfold cubeArithmeticSum
  exact sum_amplitudeRows rows slots U cap mesh hm widths Q _

/-- A uniform class bound controls the full sum through the finite amplitude alphabet. -/
theorem cubeArithmeticSum_class_uniform {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→ Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→ P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0< mesh) (hcap : cap≤1/2) (widths : Slot→ℝ) (Q : FreeRow→ Slot→ℂ)
    (A : ℝ) (hA : 0≤ A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty →
      ‖cubeArithmeticSum S hS hmax η (amplitudeRows rows slots U cap mesh hm widths Q bin)
        T hT W Yp a e t‖≤ A) :
    ‖cubeArithmeticSum S hS hmax η rows T hT W Yp a e t‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [cubeArithmeticSum_amplitude_partition S hS hmax η rows T hT W Yp a e t slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,cubeArithmeticSum,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm
end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => Eisenstein.O
variable (M : Ideal O)
variable (H : Subgroup (O ⧸ M)ˣ)

/-- The physical slot scale equals the fixed-exponent ray amplitude. -/
lemma source_physical_amplitude {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b : ℝ) (z : ℂ) (hZ : 0< Z) (hd : d≠0) (u : FreeRow) (j : Fin N) :
    physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z := by
  unfold physical
  rw [physical_slot_scale ell Z d hZ hd j]

lemma source_rowMean_eq {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0< Z) (hd : d≠0) (u : FreeRow) :
    rowMean Finset.univ (Z^d) ((2*a-1)/2) mesh (fun j=> ell j/d)
      (physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)) u=
      weightedMean Finset.univ (fun j=> ell j/d)
        (fun j=> HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z)) := by
  unfold rowMean
  simp_rw [physical_slot_scale ell Z d hZ hd,source_physical_amplitude M H ell W Z d b z hZ hd]
  rw [show (2*a-1)/2=a-1/2 by ring]

lemma source_amplitude_class_mean {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0< Z) (hd : d≠0) (hm : 0< mesh)
    (rows : Finset FreeRow) (bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh)
    (u : FreeRow)
    (hu : u∈amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=> ell j/d)
      (physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)) bin) :
    weightedMean Finset.univ (fun j=> ell j/d)
      (fun j=> HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z))=
      classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin := by
  rw [←source_rowMean_eq M H ell W Z d b a mesh z hZ hd u]
  exact rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=> ell j/d) _ bin u hu

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => Eisenstein.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Moment bounds for every retained source batch and each nonempty fiber. -/
def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=> ell j/d) → B.profile=W → B.upper=(fun _=> b) → B.external=(fun _=> z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Moments (B.fiber bin j J K hne) Δ c κ C height εm

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open Filter
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def sourceDyadExponent (Z : ℝ) (k : ℕ) : ℝ := Real.logb Z ((2:ℝ)^k)
def sourceDyadConductor (Z margin : ℝ) (k : ℕ) : ℝ := sourceDyadExponent Z k+2*margin

lemma sourceDyad_scale {Z : ℝ} (hZ : 1< Z) (k : ℕ) :
    Z^(sourceDyadExponent Z k)=(2:ℝ)^k :=
  Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by positivity)

lemma canonical_dyad_cost (loss : ℝ) (hl : 0< loss) :
    ∃C : ℝ,0< C ∧ ∀(Z v : ℝ),1≤ Z → v≤1 →
      ((smallDyadicIndices (Z^v)).card:ℝ)≤ C*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := bounded_dyadic_power_sum loss hl
  refine ⟨C,hC,?_⟩
  intro Z v hZ hv
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  calc
    _ = ∑k∈smallDyadicIndices (Z^v),(1:ℝ) := by simp
    _ ≤ ∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^loss := by
      apply Finset.sum_le_sum
      intro k hk
      exact Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hl.le
    _ ≤ C*(Z^v)^loss := hbound _ (by positivity) _ (fun k hk=> mem_smallDyadicIndices.mp hk)
    _ ≤ C*Z^loss := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

/-- Each retained norm annulus satisfies the conductor margin for its logarithmic scale. -/
lemma sourceDyad_geometry_eventually (dmin dmax margin vmax : ℝ)
    (_hdmin : 0< dmin) (hdmin1 : dmin<1/100) (hmargin : 0< margin)
    (hdmax : vmax+2*margin≤ dmax) :
    ∀ᶠZ : ℝ in atTop,∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧ rowNorm u≤ Z^vmax) →
      ∀k : ℕ,(rows∩dyadicRows 1 k).Nonempty →
        0≤ sourceDyadExponent Z k ∧ sourceDyadExponent Z k≤ vmax ∧
        dmin≤ sourceDyadConductor Z margin k ∧ sourceDyadConductor Z margin k≤ dmax ∧
        (∀u∈rows∩dyadicRows 1 k,
          Z^(sourceDyadExponent Z k)≤ rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k)) ∧
        (∀u∈rows∩dyadicRows 1 k,rowNorm u≤ Z^(sourceDyadConductor Z margin k-margin)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(1/100:ℝ)-dmin by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hsmall hmarginZ
  intro rows hrows k hne
  have hZp : 0< Z := zero_lt_one.trans hZ
  obtain ⟨u,hu⟩ := hne
  have hur := (Finset.mem_inter.mp hu).1
  have hud := mem_dyadicRows.mp (Finset.mem_inter.mp hu).2
  have hlow : (2:ℝ)^k≤ rowNorm u := by simpa only [one_mul] using hud.2.1
  have hhigh : rowNorm u<2*(2:ℝ)^k := by simpa only [one_mul] using hud.2.2
  have hv0 : 0≤ sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ,Real.rpow_zero]
    exact one_le_pow₀ (by norm_num)
  have hvmax : sourceDyadExponent Z k≤ vmax := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    exact hlow.trans (hrows u hur).2.2
  have hvmin : dmin≤ sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    have hh : 2*Z^dmin≤ Z^(1/100:ℝ) := by
      calc
        _ ≤ Z^((1/100:ℝ)-dmin)*Z^dmin := mul_le_mul_of_nonneg_right hsmall (by positivity)
        _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring
    linarith [(hrows u hur).2.1]
  have hnorm : ∀u∈rows∩dyadicRows 1 k,
      Z^(sourceDyadExponent Z k)≤ rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k) := by
    intro u hu
    rw [sourceDyad_scale hZ]
    have hh := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
    simpa only [one_mul] using And.intro hh.1 hh.2.le
  refine ⟨hv0,hvmax,?_,?_,hnorm,?_⟩
  · unfold sourceDyadConductor;linarith
  · unfold sourceDyadConductor;linarith
  · exact dyad_conductor_margin Z (sourceDyadExponent Z k) margin hZp hmarginZ _ (fun u hu=>(hnorm u hu).2)

end ProbeHighRowFamily

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
