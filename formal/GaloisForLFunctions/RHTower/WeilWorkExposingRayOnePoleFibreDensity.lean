import GaloisForLFunctions.RHTower.WeilWorkExposingRayOnePoleTransfer
import GaloisForLFunctions.RHTower.WeilWorkExposingRayFibreDensity

/-!
# Exact one-pole fibre recovery below logarithmic spectral cost

For `0 ≤ β < 1`, the weighted spectral L1 closures of every whole integer
fibre of finite positive one-pole and two-pole source mixtures coincide.
Every original row may choose either half-pole; every recovery row kills
both. All raw integer atoms, including the entire zero tail, remain exact.

The source classes and exponent range are domain conditions. No coefficient
growth, positivity, energy, RH or recovery premise is added. The full-source
case above the half exponent and the critical gamma-energy problem remain open.
-/

open MeasureTheory Filter Topology Set Finsupp Zeta23
noncomputable section
namespace RHTower.ExposingRayTransfer.OnePoleFibre
open WeilOneSided

/-- Actual compact C2 source with at least one of the two half-pole zeros. -/
def OnePoleSource := {f : WeilTestFn // ∃ s : ℝ,s^2=1/4 ∧ paperFT f.1 ((s:ℂ)*Complex.I)=0}

variable {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β < 1)

abbrev density := logDensityL1 hβ hβ1.le

/-- Whole integer fibre of finite positive actual one-pole mixtures. -/
def onePoleFibre (v : LogIndex →₀ ℝ) : Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  {ρ | ∃ c : OnePoleSource →₀ ℝ, (∀ f,0 ≤ c f) ∧
    linearCombination ℝ (fun f => logVector f.1) c=v ∧
    linearCombination ℝ (fun f => density hβ hβ1 f.1) c=ρ}

/-- Whole integer fibre with both pole zeros on every actual source. -/
def polarFibre (v : LogIndex →₀ ℝ) : Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  {ρ | ∃ c : PolarSource →₀ ℝ, (∀ f,0 ≤ c f) ∧
    linearCombination ℝ (fun f => logVector f.1) c=v ∧
    linearCombination ℝ (fun f => density hβ hβ1 f.1) c=ρ}

private def coordinateSource (j : LogIndex) (r : ℝ) : PolarSource := by
  let s := r * Real.sqrt j / (2*resonatorMass j)
  have hp := isPolarTest_twoPointResonator j.2 s
  have hs : HasCompactSupport (twoPointResonator j s) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hp.2.2.1
  exact ⟨⟨twoPointResonator j s, hp.2.1, hs⟩, _, hp⟩

private theorem coordinateSource_trace (j : LogIndex) (r : ℝ) :
    logVector (coordinateSource j r).1 = Finsupp.single j r := by
  classical
  ext k
  rw [logVector_apply]
  change atomCoeff (twoPointResonator j (r*Real.sqrt j/(2*resonatorMass j))) k /
    Real.sqrt k = (Finsupp.single j r) k
  rw [atomCoeff_twoPointResonator j.2 _ k.2]
  by_cases h : k=j
  · subst k
    rw [if_pos (show (j : ℕ)=(j : ℕ) from rfl), Finsupp.single_eq_same]
    have hm := (resonatorMass_pos j).ne'
    have hj : Real.sqrt (j : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<j.1 by omega))).ne'
    field_simp [hm,hj]
  · have hval : k.1 ≠ j.1 := fun he => h (Subtype.ext he)
    simp [hval, Ne.symm h]

private theorem trace_reachable (v : LogIndex →₀ ℝ) :
    ∃ c : PolarSource →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      linearCombination ℝ (fun f => logVector f.1) c = v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0, fun _ => le_rfl, by simp⟩
  | add v w hv hw =>
    obtain ⟨c,hc,ht⟩ := hv
    obtain ⟨d,hd,hu⟩ := hw
    exact ⟨c+d, fun f => add_nonneg (hc f) (hd f), by rw [map_add,ht,hu]⟩
  | single j r =>
    exact ⟨Finsupp.single (coordinateSource j r) 1,
      fun f => by simp only [Finsupp.single_apply]; split_ifs <;> positivity,
      by simp [coordinateSource_trace]⟩

theorem polarFibre_nonempty (v : LogIndex →₀ ℝ) : (polarFibre hβ hβ1 v).Nonempty := by
  obtain ⟨c,hc,ht⟩ := trace_reachable v
  exact ⟨_,c,hc,ht,rfl⟩

private theorem polarFibre_convex (v : LogIndex →₀ ℝ) : Convex ℝ (polarFibre hβ hβ1 v) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨c,hc,ht,hx⟩ := hx
  obtain ⟨d,hd,hu,hy⟩ := hy
  refine ⟨a • c+b • d, fun f => add_nonneg (mul_nonneg ha (hc f)) (mul_nonneg hb (hd f)), ?_, ?_⟩
  · rw [map_add,map_smul,map_smul,ht,hu,← add_smul,hab,one_smul]
  · rw [map_add,map_smul,map_smul,hx,hy]

private theorem support_fibre {ι J : Type*} (T : ι → J →₀ ℝ) (D : ι → ℝ)
    (hn : ∀ j, ∃ i, T i = Finsupp.single j (-1))
    (hp : ∀ j, ∃ i, T i = Finsupp.single j 1)
    (v : J →₀ ℝ) (s : ℝ)
    (hex : ∃ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) ∧ linearCombination ℝ T c = v)
    (hb : ∀ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) → linearCombination ℝ T c = v →
      s ≤ linearCombination ℝ D c) :
    ∃ b : J → ℝ, s ≤ linearCombination ℝ b v ∧
      ∀ i, linearCombination ℝ b (T i) ≤ D i := by
  classical
  obtain ⟨c₀,hc₀,hT₀⟩ := hex
  have hbase := hb c₀ hc₀ hT₀
  have hnull : ∀ c : ι →₀ ℝ, (∀ i, 0 ≤ c i) → linearCombination ℝ T c = 0 →
      0 ≤ linearCombination ℝ D c := by
    intro c hc hTc
    by_contra hneg
    have hd : linearCombination ℝ D c < 0 := lt_of_not_ge hneg
    let t := (linearCombination ℝ D c₀-s+1)/(-linearCombination ℝ D c)
    have ht : 0 ≤ t := div_nonneg (by linarith) (by linarith)
    have htd : t*linearCombination ℝ D c = -(linearCombination ℝ D c₀-s+1) := by
      dsimp [t]; field_simp [ne_of_lt hd]
    have he := hb (c₀+t • c) (fun i => add_nonneg (hc₀ i) (mul_nonneg ht (hc i)))
      (by rw [map_add,map_smul,hT₀,hTc,smul_zero,add_zero])
    rw [map_add,map_smul,smul_eq_mul,htd] at he
    linarith
  let T' : Option ι → J →₀ ℝ := Option.elim' (-v) T
  let D' : Option ι → ℝ := Option.elim' (-s) D
  have hTsome : T' ∘ Option.some = T := rfl
  have hDsome : D' ∘ Option.some = D := rfl
  obtain ⟨b,hb'⟩ := GaloisForLFunctions.HTGeometry.exists_of_nonneg_on_null_cone T' D'
    (fun j => by obtain ⟨i,hi⟩ := hn j; exact ⟨some i,1,by norm_num,hi⟩)
    (fun j => by obtain ⟨i,hi⟩ := hp j; exact ⟨some i,1,by norm_num,hi⟩)
    (by
      intro c hc hTc
      have hs : ∀ i, 0 ≤ c.some i := fun i => hc (some i)
      have hα : 0 ≤ c none := hc none
      rw [Finsupp.linearCombination_option, hTsome] at hTc
      rw [Finsupp.linearCombination_option, hDsome]
      change c none • (-v)+linearCombination ℝ T c.some = 0 at hTc
      change c none*(-s)+linearCombination ℝ D c.some ≥ 0
      have hTv : linearCombination ℝ T c.some = c none • v := by
        exact (show c none • v = linearCombination ℝ T c.some by
          simpa only [smul_neg,neg_add_eq_zero] using hTc).symm
      rcases eq_or_lt_of_le hα with he | he
      · have hz : c none = 0 := he.symm
        rw [hz,zero_smul] at hTv
        simpa [hz] using hnull c.some hs hTv
      · have hv : linearCombination ℝ T ((c none)⁻¹ • c.some) = v := by
          rw [map_smul,hTv,smul_smul,inv_mul_cancel₀ he.ne',one_smul]
        have hv' := hb ((c none)⁻¹ • c.some)
          (fun i => mul_nonneg (inv_nonneg.mpr hα) (hs i)) hv
        rw [map_smul,smul_eq_mul] at hv'
        have hmul := mul_le_mul_of_nonneg_left hv' hα
        rw [← mul_assoc,mul_inv_cancel₀ he.ne',one_mul] at hmul
        nlinarith)
  refine ⟨b, ?_, fun i => hb' (some i)⟩
  have he := hb' none
  change linearCombination ℝ b (-v) ≤ -s at he
  rw [map_neg] at he
  linarith


private def natWeights (b : LogIndex → ℝ) (n : ℕ) : ℝ :=
  if h : 2 ≤ n then b ⟨n,h⟩ else 0

private def rawWeights (b : LogIndex → ℝ) (n : ℕ) : ℝ := natWeights b n / Real.sqrt n

private theorem pairing_eq_atomValue (b : LogIndex → ℝ) (f : WeilTestFn) :
    linearCombination ℝ b (logVector f) = atomValue (rawWeights b) f.1 := by
  have he : weilFullFunctional (natWeights b) (Zeta23.EF.weilTest f.1 f.1) -
      weilFullFunctional (fun _ => 0) (Zeta23.EF.weilTest f.1 f.1) =
      atomicForm (rawWeights b) 0 (Zeta23.EF.weilTest f.1 f.1) := by
    unfold weilFullFunctional atomicForm rawWeights
    simp only [zero_div,ite_self,Complex.ofReal_zero,zero_mul,tsum_zero,sub_zero]
    ring
  have hl : (fun j : LogIndex => natWeights b j) = b := by
    funext j; simp only [natWeights,dif_pos j.2]
  have hh := congrArg Complex.re he
  rw [Complex.sub_re,re_weilFullFunctional_eq,re_weilFullFunctional_eq,hl] at hh
  have hz : linearCombination ℝ (fun _ : LogIndex => (0 : ℝ)) (logVector f) = 0 := by
    simp [linearCombination_apply]
  rw [hz] at hh
  unfold atomValue
  linarith

private def polarToOne (p : PolarSource) : OnePoleSource := by
  refine ⟨p.1,1/2,by norm_num,?_⟩
  obtain ⟨a,ha⟩ := p.2
  have he : (((1/2:ℝ):ℂ)*Complex.I) = Complex.I/2 := by push_cast; ring
  rw [he]
  exact ha.2.2.2.1

private theorem polarFibre_subset_onePoleFibre (v : LogIndex →₀ ℝ) :
    polarFibre hβ hβ1 v ⊆ onePoleFibre hβ hβ1 v := by
  intro ρ hρ
  obtain ⟨c,hc,ht,hρ⟩ := hρ
  refine ⟨c.mapDomain polarToOne,Finsupp.mapDomain_nonneg hc,?_,?_⟩
  · rw [Finsupp.linearCombination_mapDomain]
    exact ht
  · rw [Finsupp.linearCombination_mapDomain]
    exact hρ

private theorem onePole_pairing_bound (b : LogIndex → ℝ)
    (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    (h : ∀ p : PolarSource,linearCombination ℝ b (logVector p.1) ≤ ell (density hβ hβ1 p.1)) :
    ∀ f : OnePoleSource,linearCombination ℝ b (logVector f.1) ≤ ell (density hβ hβ1 f.1) := by
  have hp : ∀ f : WeilTestFn,(∃ a,IsPolarTest a f.1) →
      atomValue (rawWeights b) f.1 ≤ ell (logDensityL1 hβ hβ1.le f) := by
    intro f hf
    rw [← pairing_eq_atomValue]
    exact h ⟨f,hf⟩
  intro f
  obtain ⟨s,hs,hzero⟩ := f.2
  rw [pairing_eq_atomValue]
  exact log_separator_onePole hβ hβ1 hs hp f.1 hzero

private theorem onePoleFibre_subset_closure_polarFibre (v : LogIndex →₀ ℝ) :
    onePoleFibre hβ hβ1 v ⊆ closure (polarFibre hβ hβ1 v) := by
  intro ρ hρ
  obtain ⟨c,hc,ht,hρ⟩ := hρ
  by_contra hn
  obtain ⟨ell,s,hs,hsep⟩ := geometric_hahn_banach_point_closed
    (polarFibre_convex hβ hβ1 v).closure isClosed_closure hn
  let T : PolarSource → LogIndex →₀ ℝ := fun p => logVector p.1
  let D : PolarSource → ℝ := fun p => ell (density hβ hβ1 p.1)
  have hcost : ∀ d : PolarSource →₀ ℝ,(∀ p,0 ≤ d p) →
      linearCombination ℝ T d=v → s ≤ linearCombination ℝ D d := by
    intro d hd htd
    have he := (hsep (linearCombination ℝ (fun p : PolarSource => density hβ hβ1 p.1) d)
      (subset_closure ⟨d,hd,htd,rfl⟩)).le
    have hmap := Finsupp.apply_linearCombination ℝ ell.toLinearMap
      (fun p : PolarSource => density hβ hβ1 p.1) d
    change ell (linearCombination ℝ (fun p : PolarSource => density hβ hβ1 p.1) d) =
      linearCombination ℝ D d at hmap
    rwa [hmap] at he
  obtain ⟨b,hbv,hb⟩ := support_fibre T D
    (fun j => ⟨coordinateSource j (-1),coordinateSource_trace j (-1)⟩)
    (fun j => ⟨coordinateSource j 1,coordinateSource_trace j 1⟩)
    v s (trace_reachable v) hcost
  have hsource := onePole_pairing_bound hβ hβ1 b ell hb
  have hsum : linearCombination ℝ (fun f : OnePoleSource => linearCombination ℝ b (logVector f.1)) c ≤
      linearCombination ℝ (fun f : OnePoleSource => ell (density hβ hβ1 f.1)) c := by
    simp only [linearCombination_apply,Finsupp.sum,smul_eq_mul]
    exact Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hsource f) (hc f)
  have hl := Finsupp.apply_linearCombination ℝ (linearCombination ℝ b)
    (fun f : OnePoleSource => logVector f.1) c
  have hr := Finsupp.apply_linearCombination ℝ ell.toLinearMap
    (fun f : OnePoleSource => density hβ hβ1 f.1) c
  change linearCombination ℝ b (linearCombination ℝ (fun f : OnePoleSource => logVector f.1) c) =
    linearCombination ℝ (fun f : OnePoleSource => linearCombination ℝ b (logVector f.1)) c at hl
  change ell (linearCombination ℝ (fun f : OnePoleSource => density hβ hβ1 f.1) c) =
    linearCombination ℝ (fun f : OnePoleSource => ell (density hβ hβ1 f.1)) c at hr
  rw [← hl,← hr,ht,hρ] at hsum
  linarith

/-- Both pole zeros can be imposed without changing any exact whole fibre closure. -/
theorem closure_polarFibre_eq_onePoleFibre (v : LogIndex →₀ ℝ) :
    closure (polarFibre hβ hβ1 v) = closure (onePoleFibre hβ hβ1 v) := by
  apply le_antisymm
  · exact closure_mono (polarFibre_subset_onePoleFibre hβ hβ1 v)
  · exact closure_minimal (onePoleFibre_subset_closure_polarFibre hβ hβ1 v) isClosed_closure

/-- Arbitrary weighted recovery of each actual finite positive one-pole mixture,
with the whole integer trace exact and both zeros on every recovery row. -/
theorem exists_exact_fibre_recovery (c : OnePoleSource →₀ ℝ) (hc : ∀ f,0 ≤ c f)
    {ε : ℝ} (hε : 0<ε) :
    ∃ d : PolarSource →₀ ℝ,(∀ p,0 ≤ d p) ∧
      linearCombination ℝ (fun p => logVector p.1) d =
        linearCombination ℝ (fun f => logVector f.1) c ∧
      ‖linearCombination ℝ (fun p => density hβ hβ1 p.1) d-
        linearCombination ℝ (fun f => density hβ hβ1 f.1) c‖ < ε := by
  have hm := onePoleFibre_subset_closure_polarFibre hβ hβ1
    (linearCombination ℝ (fun f : OnePoleSource => logVector f.1) c)
    (show linearCombination ℝ (fun f : OnePoleSource => density hβ hβ1 f.1) c ∈
      onePoleFibre hβ hβ1 (linearCombination ℝ (fun f : OnePoleSource => logVector f.1) c) from
      ⟨c,hc,rfl,rfl⟩)
  obtain ⟨ρ,hρ,hε'⟩ := Metric.mem_closure_iff.mp hm ε hε
  obtain ⟨d,hd,ht,hρ⟩ := hρ
  refine ⟨d,hd,ht,?_⟩
  rw [hρ,← dist_eq_norm,dist_comm]
  exact hε'

private theorem trace_coordinate {ι : Type*} (F : ι → WeilTestFn) (c : ι →₀ ℝ)
    (j : LogIndex) :
    (linearCombination ℝ (fun i => logVector (F i)) c) j =
      linearCombination ℝ (fun i => atomCoeff (F i).1 j) c / Real.sqrt j := by
  classical
  simp only [linearCombination_apply,Finsupp.sum,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    logVector_apply,logValue,smul_eq_mul,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  change c i * (atomCoeff (F i).1 j / Real.sqrt j) = c i * atomCoeff (F i).1 j / Real.sqrt j
  ring


/-- Every raw integer atom is preserved, including the entire zero tail. -/
theorem exists_raw_fibre_recovery (c : OnePoleSource →₀ ℝ) (hc : ∀ f,0 ≤ c f)
    {ε : ℝ} (hε : 0<ε) :
    ∃ d : PolarSource →₀ ℝ,(∀ p,0 ≤ d p) ∧
      (∀ n : ℕ,2 ≤ n → linearCombination ℝ (fun p => atomCoeff p.1.1 n) d =
        linearCombination ℝ (fun f => atomCoeff f.1.1 n) c) ∧
      ‖linearCombination ℝ (fun p => density hβ hβ1 p.1) d-
        linearCombination ℝ (fun f => density hβ hβ1 f.1) c‖ < ε := by
  obtain ⟨d,hd,ht,he⟩ := exists_exact_fibre_recovery hβ hβ1 c hc hε
  refine ⟨d,hd,?_,he⟩
  intro n hn
  have h := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n,hn⟩) ht
  rw [trace_coordinate (fun p : PolarSource => p.1),trace_coordinate (fun f : OnePoleSource => f.1)] at h
  have hn0 : Real.sqrt (n:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))).ne'
  exact (div_left_inj' hn0).mp h

end RHTower.ExposingRayTransfer.OnePoleFibre
