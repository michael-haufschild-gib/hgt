import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarSourceIdentification
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamLaurentMaster

/-!
# Exact three-field reconstruction of the original scalar response

All four original sourced Laurent reconstruction amplitudes are expressed using only the
constant angular action and the two simple resolvents at shifts two and `(2s+1)(2s+2)`.
The reduction retains actual twisted radial derivatives and proves smoothness of every radial
column. Physical noncollision is derived for both original Xi branches. The full nonseparated
metric equation and causal endpoint admission are separate obligations.
-/

open Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.TwistedRadial
open scoped ContDiff
namespace RHTower.D4BMThreeFieldReconstruction
open D4BMScalarStream D4BMScalarSourceIdentification
noncomputable section
set_option autoImplicit false

/-- The physical target angular shift. -/
def targetShift (s : ℂ) : ℂ := (2*s+1)*(2*s+2)

/-- Regular part of the master plus twice the radius times its trace-free source. -/
def reducedMaster0 (s r : ℂ) : ℂ :=
  r+s*(3*s+2)/(2*r)+s^(2 : ℕ)*(s+1)^(2 : ℕ)/(8*r^(3 : ℕ))

/-- Residue of that same reduced master at its other angular shift. -/
def reducedMasterD (s r : ℂ) : ℂ := 3*s*(s+1)^(2 : ℕ)*(3*s+4)/(2*r)

/-- Actual first twisted radial expression of the regular coefficient. -/
def reducedMaster01 (s r : ℂ) : ℂ :=
  1-s*(3*s+2)/(2*r^(2 : ℕ))-3*s^(2 : ℕ)*(s+1)^(2 : ℕ)/(8*r^(4 : ℕ))+2*s/(r*(r^(2 : ℕ)-1))*reducedMaster0 s r

/-- Actual first twisted radial expression of the residue coefficient. -/
def reducedMasterD1 (s r : ℂ) : ℂ :=
  -reducedMasterD s r/r+2*s/(r*(r^(2 : ℕ)-1))*reducedMasterD s r

private def tensorCoefficient1 (s r : ℂ) : ℂ :=
  s^(2 : ℕ)/r^(3 : ℕ)-s^(2 : ℕ)*(s+1)^(2 : ℕ)/(2*r^(5 : ℕ))+2*s/(r*(r^(2 : ℕ)-1))*tensorCoefficient s r

private theorem sourceTF1_factor (s r μ : ℂ) (hr : r ≠ 0)
    (hf : r^(2 : ℕ)-1 ≠ 0) (hμ : 2-μ ≠ 0) :
    ssSourceTF1 s r μ = tensorCoefficient1 s r*(1+(s+1)*(s+2)/(2-μ)) := by
  unfold ssSourceTF1 tensorCoefficient1 tensorCoefficient
  field_simp
  ring

/-- The entire shift-two pole cancels in the original source-retaining master combination. -/
theorem reducedMaster_eq (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) {r : ℝ} (hr1 : 1 < r) :
    ssLaurentMaster s μ r+2*r*srcTF s μ r =
      reducedMaster0 s r+reducedMasterD s r/(μ-targetShift s) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  rw [srcTF_eq s μ hr1 hs hμ,ssSourceTF_factor s r μ hr hμ]
  unfold ssLaurentMaster laurentMasterField
  rw [laurentMasterA_resolvents s μ hμ hres,laurentMasterB_resolvent s μ hμ]
  unfold reducedMaster0 reducedMasterD targetShift tensorCoefficient
  field_simp
  ring

/-- The cancellation retains the complete original twisted radial derivative. -/
theorem reducedMaster_twist_eq (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) {r : ℝ} (hr1 : 1 < r) :
    twist s (ssLaurentMaster s μ) r+2*srcTF s μ r+2*r*twist s (srcTF s μ) r =
      reducedMaster01 s r+reducedMasterD1 s r/(μ-targetShift s) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  rw [twist_srcTF s μ hr1,srcTF1_eq s μ hr1 hs hμ,srcTF_eq s μ hr1 hs hμ,
    sourceTF1_factor s r μ hr hf hμ,ssSourceTF_factor s r μ hr hμ]
  simp only [ssLaurentMaster,twist,(hasDerivAt_laurentMasterField _ _ hr).deriv]
  unfold laurentMasterFirst laurentMasterField
  rw [laurentMasterA_resolvents s μ hμ hres,laurentMasterB_resolvent s μ hμ]
  unfold reducedMaster01 reducedMasterD1 reducedMaster0 reducedMasterD
    targetShift tensorCoefficient1 tensorCoefficient
  field_simp
  ring

/-- Constant angular part of the actual reconstructed metric amplitude. -/
def metricH0 (s r : ℂ) : ℂ := reducedMaster0 s r/(4*r)

/-- The physical-shift part of the same reconstructed amplitude. -/
def metricHD (s r : ℂ) : ℂ :=
  ((r^(2 : ℕ)-1)/2*reducedMasterD1 s r-targetShift s*reducedMasterD s r/(4*r))/(2-targetShift s)

/-- The shift-two part, retaining both original source rows. -/
def metricH2 (s r : ℂ) : ℂ :=
  (r^(2 : ℕ)-1)/2*reducedMaster01 s r-reducedMaster0 s r/(2*r)-
    r*(r^(2 : ℕ)-1)/(2*s)*ssSourceTR s r 0-(r^(2 : ℕ)-1)/s*ssSourceT s r 0-
    reducedMasterD s r/(4*r)+metricHD s r

/-- The original sourced radial reconstruction, before simplification. -/
def originalH (s μ : ℂ) : ℝ → ℂ :=
  recHR s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ)
    (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)

private theorem originalH_formula (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalH s μ r =
      (((r:ℂ)^(2 : ℕ)-1)/2*(twist s (ssLaurentMaster s μ) r+2*srcTF s μ r+2*r*twist s (srcTF s μ) r)-
        μ/(4*r)*(ssLaurentMaster s μ r+2*r*srcTF s μ r)-
        r*((r:ℂ)^(2 : ℕ)-1)/(2*s)*srcTR s μ r-((r:ℂ)^(2 : ℕ)-1)/s*srcT s μ r)/(2-μ) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  unfold originalH
  rw [recHR_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ]
  simp only [recH,twistIter_succ,twistIter_zero]
  field_simp
  ring

/-- Exact three-field decomposition of the original reconstructed angular metric amplitude. -/
theorem originalH_three_fields (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalH s μ r = metricH0 s r+metricH2 s r/(2-μ)+metricHD s r/(μ-targetShift s) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  rw [originalH_formula s μ hs hμ hr1,reducedMaster_twist_eq s μ hs hμ hres hr1,
    reducedMaster_eq s μ hs hμ hres hr1,srcTR_eq s μ hr1 hs hμ,srcT_eq s μ hr1 hs hμ]
  unfold metricH0 metricH2 metricHD
  change (((r:ℂ)^(2 : ℕ)-1)/2*(reducedMaster01 s r+reducedMasterD1 s r/(μ-targetShift s))-
    μ/(4*r)*(reducedMaster0 s r+reducedMasterD s r/(μ-targetShift s))-
    r*((r:ℂ)^(2 : ℕ)-1)/(2*s)*ssSourceTR s r 0-((r:ℂ)^(2 : ℕ)-1)/s*ssSourceT s r 0)/(2-μ) = _
  field_simp
  ring

/-- The original temporal-radial reconstructed coefficient. -/
def originalF1 (s μ : ℂ) : ℝ → ℂ :=
  recF1R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ)
    (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)

/-- The original radial reconstructed coefficient. -/
def originalF2 (s μ : ℂ) : ℝ → ℂ :=
  recF2R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ)
    (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)

/-- The original temporal reconstructed coefficient. -/
def originalF0 (s μ : ℂ) : ℝ → ℂ :=
  recF0R s μ (ssLaurentMaster s μ) (srcTT s μ) (srcTR s μ) (srcRR s μ)
    (srcT s μ) (srcR s μ) (srcTF s μ) (srcL s μ)

private theorem originalF1_formula (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalF1 s μ r = s/((r:ℂ)^(2 : ℕ)-1)*(4*r*originalH s μ r-
      (ssLaurentMaster s μ r+2*r*srcTF s μ r)) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  unfold originalF1 originalH
  rw [recF1R_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ,recHR_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ]
  simp only [recF1,recH,twistIter_succ,twistIter_zero]
  field_simp
  ring

private theorem originalF2_formula (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalF2 s μ r = -r/(2*s*((r:ℂ)^(2 : ℕ)-1))*srcTR s μ r+
      μ/(4*s*r*((r:ℂ)^(2 : ℕ)-1))*originalF1 s μ r-
      2/((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*originalH s μ r+2*r/((r:ℂ)^(2 : ℕ)-1)*twist s (originalH s μ) r := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  have hM : TwistSmooth s (ssLaurentMaster s μ) 2 :=
    fun r hr k _ => differentiableAt_twistIter s (ssLaurentMaster_contDiffOn s μ) k hr
  unfold originalF2 originalF1 originalH
  rw [twist_recHR s μ _ _ _ _ _ _ _ _ hr1 hM (srcTR_twistSmooth s μ 1)
    (srcT_twistSmooth s μ 1) (srcTF_twistSmooth s μ 2),
    recF2R_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ,recF1R_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ,
    recHR_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ,recH1R_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ]
  simp only [recF2,recF1,recH,recH1,twistIter_succ,twistIter_zero]
  field_simp
  ring

private theorem originalF0_formula (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalF0 s μ r = ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*originalF2 s μ r-2*((r:ℂ)^(2 : ℕ)-1)*srcTF s μ r := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  unfold originalF0 originalF2
  rw [recF0R_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ,recF2R_eq s μ _ _ _ _ _ _ _ _ hr1 hs hμ]
  simp only [recF0,recF2,twistIter_succ,twistIter_zero]
  field_simp
  ring

/-- Shift-two coefficient of the original temporal-radial amplitude. -/
def metricF12 (s r : ℂ) : ℂ := 4*s*r/((r:ℂ)^(2 : ℕ)-1)*metricH2 s r

/-- Physical-shift coefficient of the original temporal-radial amplitude. -/
def metricF1D (s r : ℂ) : ℂ := s/(r^(2 : ℕ)-1)*(4*r*metricHD s r-reducedMasterD s r)

/-- The temporal-radial metric coefficient has only the two proper resolvents. -/
theorem originalF1_two_fields (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalF1 s μ r = metricF12 s r/(2-μ)+metricF1D s r/(μ-targetShift s) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  rw [originalF1_formula s μ hs hμ hr1,originalH_three_fields s μ hs hμ hres hshift hr1,
    reducedMaster_eq s μ hs hμ hres hr1]
  unfold metricF12 metricF1D metricH0
  field_simp
  ring

/-- Smoothness of all three original angular-metric coefficients on the exterior. -/
theorem metricH_smooth (s : ℂ) :
    ContDiffOn ℝ ∞ (fun r : ℝ => metricH0 s r) (Ioi 1) ∧
    ContDiffOn ℝ ∞ (fun r : ℝ => metricH2 s r) (Ioi 1) ∧
    ContDiffOn ℝ ∞ (fun r : ℝ => metricHD s r) (Ioi 1) := by
  have hr (r : ℝ) (h : r ∈ Ioi (1:ℝ)) : (r:ℂ) ≠ 0 := (exterior_ne r h).1
  have hf (r : ℝ) (h : r ∈ Ioi (1:ℝ)) : (r:ℂ)^(2 : ℕ)-1 ≠ 0 := (exterior_ne r h).2
  constructor
  · intro r h
    apply ContDiffAt.contDiffWithinAt
    have hR := hr r h
    have hF := hf r h
    unfold metricH0 reducedMaster0
    simp only [div_eq_mul_inv,mul_inv]
    fun_prop (disch := aesop)
  constructor
  · intro r h
    apply ContDiffAt.contDiffWithinAt
    have hR := hr r h
    have hF := hf r h
    unfold metricH2 metricHD reducedMaster01 reducedMasterD1 reducedMaster0 reducedMasterD
      ssSourceTR ssSourceT
    simp only [div_eq_mul_inv,mul_inv]
    fun_prop (disch := aesop)
  · intro r h
    apply ContDiffAt.contDiffWithinAt
    have hR := hr r h
    have hF := hf r h
    unfold metricHD reducedMasterD1 reducedMasterD
    simp only [div_eq_mul_inv,mul_inv]
    fun_prop (disch := aesop)

private theorem originalH_twist_three_fields (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    twist s (originalH s μ) r =
      twist s (fun r : ℝ => metricH0 s r) r+
      twist s (fun r : ℝ => metricH2 s r) r/(2-μ)+
      twist s (fun r : ℝ => metricHD s r) r/(μ-targetShift s) := by
  have he : originalH s μ =ᶠ[𝓝 r] (fun r : ℝ =>
      metricH0 s r+metricH2 s r/(2-μ)+metricHD s r/(μ-targetShift s)) := by
    filter_upwards [exterior_eventually hr1] with t ht
    exact originalH_three_fields s μ hs hμ hres hshift ht
  rw [twist_congr s he]
  obtain ⟨h0,h2,hD⟩ := metricH_smooth s
  have hd0 := ((h0.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hr1)).hasDerivAt
  have hd2 := ((h2.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hr1)).hasDerivAt
  have hdD := ((hD.differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hr1)).hasDerivAt
  unfold twist
  have hder := ((hd0.add (hd2.div_const (2-μ))).add (hdD.div_const (μ-targetShift s))).deriv
  change deriv (fun t : ℝ => metricH0 s t+metricH2 s t/(2-μ)+metricHD s t/(μ-targetShift s)) r = _ at hder
  rw [hder]
  ring


/-- Regular radial metric coefficient. -/
def metricF20 (s : ℂ) (r : ℝ) : ℂ :=
  -r/(2*s*((r:ℂ)^(2 : ℕ)-1))*ssSourceTR s r 0+
    (metricF1D s r-metricF12 s r)/(4*s*r*((r:ℂ)^(2 : ℕ)-1))-
    2/((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*metricH0 s r+
    2*r/((r:ℂ)^(2 : ℕ)-1)*twist s (fun r : ℝ => metricH0 s r) r

/-- Shift-two radial metric coefficient. -/
def metricF22 (s : ℂ) (r : ℝ) : ℂ :=
  metricF12 s r/(2*s*r*((r:ℂ)^(2 : ℕ)-1))-
    2/((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*metricH2 s r+
    2*r/((r:ℂ)^(2 : ℕ)-1)*twist s (fun r : ℝ => metricH2 s r) r

/-- Physical-shift radial metric coefficient. -/
def metricF2D (s : ℂ) (r : ℝ) : ℂ :=
  targetShift s*metricF1D s r/(4*s*r*((r:ℂ)^(2 : ℕ)-1))-
    2/((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*metricHD s r+
    2*r/((r:ℂ)^(2 : ℕ)-1)*twist s (fun r : ℝ => metricHD s r) r

/-- Regular temporal metric coefficient. -/
def metricF00 (s : ℂ) (r : ℝ) : ℂ :=
  ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*metricF20 s r-2*((r:ℂ)^(2 : ℕ)-1)*tensorCoefficient s r

/-- Shift-two temporal metric coefficient. -/
def metricF02 (s : ℂ) (r : ℝ) : ℂ :=
  ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*metricF22 s r-2*((r:ℂ)^(2 : ℕ)-1)*(s+1)*(s+2)*tensorCoefficient s r

/-- Physical-shift temporal metric coefficient. -/
def metricF0D (s : ℂ) (r : ℝ) : ℂ := ((r:ℂ)^(2 : ℕ)-1)^(2 : ℕ)*metricF2D s r

/-- Exact three-field decomposition of the original radial metric coefficient. -/
theorem originalF2_three_fields (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalF2 s μ r = metricF20 s r+metricF22 s r/(2-μ)+metricF2D s r/(μ-targetShift s) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  rw [originalF2_formula s μ hs hμ hr1,originalF1_two_fields s μ hs hμ hres hshift hr1,
    originalH_three_fields s μ hs hμ hres hshift hr1,
    originalH_twist_three_fields s μ hs hμ hres hshift hr1,srcTR_eq s μ hr1 hs hμ]
  rw [show ssSourceTR s (r:ℂ) μ = ssSourceTR s (r:ℂ) 0 from rfl]
  unfold metricF20 metricF22 metricF2D
  field_simp
  ring

/-- Exact three-field decomposition of the original temporal metric coefficient. -/
theorem originalF0_three_fields (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) :
    originalF0 s μ r = metricF00 s r+metricF02 s r/(2-μ)+metricF0D s r/(μ-targetShift s) := by
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  rw [originalF0_formula s μ hs hμ hr1,originalF2_three_fields s μ hs hμ hres hshift hr1,
    srcTF_eq s μ hr1 hs hμ,ssSourceTF_factor s r μ hr hμ]
  unfold metricF00 metricF02 metricF0D
  field_simp
  ring

/-- Three radial columns, each ordered as temporal, temporal-radial, radial and angular amplitudes. -/
def radialColumn (s : ℂ) : Fin 3 → Fin 4 → ℝ → ℂ :=
  ![![metricF00 s,fun _ => 0,metricF20 s,fun r => metricH0 s r],
    ![metricF02 s,fun r => metricF12 s r,metricF22 s,fun r => metricH2 s r],
    ![metricF0D s,fun r => metricF1D s r,metricF2D s,fun r => metricHD s r]]

/-- Every radial coefficient has every exterior derivative; no regularity premise is supplied. -/
theorem radialColumn_smooth (s : ℂ) (k : Fin 3) (j : Fin 4) :
    ContDiffOn ℝ ∞ (radialColumn s k j) (Ioi 1) := by
  intro r hr1
  apply ContDiffAt.contDiffWithinAt
  obtain ⟨hr,hf⟩ := exterior_ne r hr1
  obtain ⟨h0,h2,hD⟩ := metricH_smooth s
  have hH0 := h0.contDiffAt (isOpen_Ioi.mem_nhds hr1)
  have hH2 := h2.contDiffAt (isOpen_Ioi.mem_nhds hr1)
  have hHD := hD.contDiffAt (isOpen_Ioi.mem_nhds hr1)
  have hT0 := (contDiffOn_twist s h0).contDiffAt (isOpen_Ioi.mem_nhds hr1)
  have hT2 := (contDiffOn_twist s h2).contDiffAt (isOpen_Ioi.mem_nhds hr1)
  have hTD := (contDiffOn_twist s hD).contDiffAt (isOpen_Ioi.mem_nhds hr1)
  have hκ : ContDiffAt ℝ ∞ (fun r : ℝ => tensorCoefficient s r) r := by
    unfold tensorCoefficient
    simp only [div_eq_mul_inv,mul_inv]
    fun_prop (disch := aesop)
  have hTR : ContDiffAt ℝ ∞ (fun r : ℝ => ssSourceTR s r 0) r := by
    unfold ssSourceTR
    simp only [div_eq_mul_inv,mul_inv]
    fun_prop (disch := aesop)
  fin_cases k <;> fin_cases j
  all_goals simp only [radialColumn,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk]
  all_goals try delta metricF00 metricF02 metricF0D metricF20 metricF22 metricF2D metricF12 metricF1D reducedMasterD
  all_goals try simp only [div_eq_mul_inv,mul_inv]
  all_goals fun_prop (disch := aesop)


/-- Original reconstruction amplitudes in the same order as each radial column. -/
def originalRadialColumn (s μ : ℂ) : Fin 4 → ℝ → ℂ :=
  ![originalF0 s μ,originalF1 s μ,originalF2 s μ,originalH s μ]

/-- The original reconstruction is exactly a regular column and two simple resolvent columns. -/
theorem originalRadialColumn_three_fields (s μ : ℂ) (hs : s ≠ 0) (hμ : 2-μ ≠ 0)
    (hres : μ-targetShift s ≠ 0) (hshift : 2-targetShift s ≠ 0)
    {r : ℝ} (hr1 : 1 < r) (j : Fin 4) :
    originalRadialColumn s μ j r = radialColumn s 0 j r+
      radialColumn s 1 j r/(2-μ)+radialColumn s 2 j r/(μ-targetShift s) := by
  fin_cases j <;> simp only [originalRadialColumn,radialColumn,Matrix.cons_val',
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons,Fin.reduceFinMk,zero_add]
  · exact originalF0_three_fields s μ hs hμ hres hshift hr1
  · exact originalF1_two_fields s μ hs hμ hres hshift hr1
  · exact originalF2_three_fields s μ hs hμ hres hshift hr1
  · exact originalH_three_fields s μ hs hμ hres hshift hr1

/-- Both original physical branches avoid zero and collision of the two angular shifts. -/
theorem physical_shifts (q : XiZeroCopy) (branch : Bool) :
    D4BMModularCore.physicalRate q branch ≠ 0 ∧
    targetShift (D4BMModularCore.physicalRate q branch) ≠ 0 ∧
    2-targetShift (D4BMModularCore.physicalRate q branch) ≠ 0 := by
  obtain ⟨hr,hi⟩ := physicalLaurentRate_bounds q branch
  refine ⟨?_,?_,?_⟩
  · intro h
    exact hi (congrArg Complex.im h)
  · have h := laurentPole_ne_zero _ hr hi 0
    simpa only [Complex.ofReal_zero,zero_sub,neg_ne_zero,targetShift] using h
  · exact laurentPole_ne_zero _ hr hi 2

/-- Unconditional specialization to every original Xi occurrence, physical branch and real angular momentum. -/
theorem physical_originalRadialColumn_three_fields (q : XiZeroCopy) (branch : Bool)
    (k : ℝ) {r : ℝ} (hr1 : 1 < r) (j : Fin 4) :
    originalRadialColumn (D4BMModularCore.physicalRate q branch) (-(k:ℂ)^(2 : ℕ)) j r =
      radialColumn (D4BMModularCore.physicalRate q branch) 0 j r+
      radialColumn (D4BMModularCore.physicalRate q branch) 1 j r/(2-(-(k:ℂ)^(2 : ℕ)))+
      radialColumn (D4BMModularCore.physicalRate q branch) 2 j r/
        (-(k:ℂ)^(2 : ℕ)-targetShift (D4BMModularCore.physicalRate q branch)) := by
  obtain ⟨hr,hi⟩ := physicalLaurentRate_bounds q branch
  obtain ⟨hs,_,hshift⟩ := physical_shifts q branch
  have hμ : (2:ℂ)-(-(k:ℂ)^(2 : ℕ)) ≠ 0 := by
    exact_mod_cast (show (2:ℝ)-(-k^(2 : ℕ)) ≠ 0 by nlinarith [sq_nonneg k])
  have hres := laurentPole_ne_zero _ hr hi (-k^(2 : ℕ))
  push_cast at hres
  exact originalRadialColumn_three_fields _ _ hs hμ hres hshift hr1 j

end
end RHTower.D4BMThreeFieldReconstruction
