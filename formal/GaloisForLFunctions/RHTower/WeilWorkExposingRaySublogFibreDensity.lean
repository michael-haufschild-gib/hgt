import GaloisForLFunctions.RHTower.WeilWorkExposingRaySublogTransfer
import GaloisForLFunctions.RHTower.WeilWorkExposingRayFibreDensity

/-!
# Exact whole integer fibres in sub-half-logarithmic weighted L1

For every 0 ≤ β < 1/2, finite positive actual full-source mixtures admit
arbitrarily accurate recovery in the weight 1 + log(2 + |t|)^β by actual
finite positive polar mixtures, preserving every raw integer atom exactly.
Both polar zeros hold on each row. No growth, RH, positivity or recovery
premise is added. The literal Fejer density has exact-null weighted recovery.

This does not control the archimedean energy, whose weight grows like log |t|.
The universal WP02 lower inequality remains open.
-/

open MeasureTheory Filter Topology Set Finsupp
noncomputable section
namespace RHTower.ExposingRayTransfer.SublogFibre
open WeilOneSided

variable {β : ℝ} (hβ : 0 ≤ β) (hβhalf : β < 1/2)

/-- Spectral density multiplied by 1 + log(2 + |t|)^β. -/
abbrev density := logDensityL1 hβ (show β ≤ 1 by linarith)

/-- Every finite positive full-source mixture in one exact whole integer fibre. -/
def fullFibre (v : LogIndex →₀ ℝ) : Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  {ρ | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
    linearCombination ℝ logVector c = v ∧ linearCombination ℝ (density hβ hβhalf) c = ρ}

/-- The same exact fibre, with both polar zeros in each actual source. -/
def polarFibre (v : LogIndex →₀ ℝ) : Set (Lp ℝ 1 (volume : Measure ℝ)) :=
  {ρ | ∃ c : PolarSource →₀ ℝ, (∀ f, 0 ≤ c f) ∧
    linearCombination ℝ (fun f => logVector f.1) c = v ∧
    linearCombination ℝ (fun f => (density hβ hβhalf) f.1) c = ρ}

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

theorem polarFibre_nonempty (v : LogIndex →₀ ℝ) : (polarFibre hβ hβhalf v).Nonempty := by
  obtain ⟨c,hc,ht⟩ := trace_reachable v
  exact ⟨_,c,hc,ht,rfl⟩

private theorem polarFibre_convex (v : LogIndex →₀ ℝ) : Convex ℝ (polarFibre hβ hβhalf v) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨c,hc,ht,hx⟩ := hx
  obtain ⟨d,hd,hu,hy⟩ := hy
  refine ⟨a • c+b • d, fun f => add_nonneg (mul_nonneg ha (hc f)) (mul_nonneg hb (hd f)), ?_, ?_⟩
  · rw [map_add,map_smul,map_smul,ht,hu,← add_smul,hab,one_smul]
  · rw [map_add,map_smul,map_smul,hx,hy]

private theorem polarFibre_subset_fullFibre (v : LogIndex →₀ ℝ) :
    polarFibre hβ hβhalf v ⊆ fullFibre hβ hβhalf v := by
  intro ρ hρ
  obtain ⟨c,hc,ht,hρ⟩ := hρ
  refine ⟨c.mapDomain Subtype.val, Finsupp.mapDomain_nonneg hc, ?_, ?_⟩
  · rw [Finsupp.linearCombination_mapDomain]
    change linearCombination ℝ (fun p : PolarSource => logVector p.1) c = v
    exact ht
  · rw [Finsupp.linearCombination_mapDomain]
    change linearCombination ℝ (fun p : PolarSource => (density hβ hβhalf) p.1) c = ρ
    exact hρ

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

private theorem full_pairing_bound (b : LogIndex → ℝ)
    (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ)
    (h : ∀ p : PolarSource, linearCombination ℝ b (logVector p.1) ≤ ell ((density hβ hβhalf) p.1)) :
    ∀ f : WeilTestFn, linearCombination ℝ b (logVector f) ≤ ell ((density hβ hβhalf) f) := by
  have hp : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue (rawWeights b) f.1 ≤ ell (logDensityL1 hβ (by linarith) f) := by
    intro f hf
    rw [← pairing_eq_atomValue]
    exact h ⟨f,hf⟩
  have hf := (polarLogSpectralBound_iff_fullLogSpectralBound hβ hβhalf (rawWeights b) ell).mp hp
  intro f
  rw [pairing_eq_atomValue]
  exact hf f

private theorem fullFibre_subset_closure_polarFibre (v : LogIndex →₀ ℝ) :
    fullFibre hβ hβhalf v ⊆ closure (polarFibre hβ hβhalf v) := by
  intro ρ hρ
  obtain ⟨c,hc,ht,hρ⟩ := hρ
  by_contra hn
  obtain ⟨ell,s,hs,hsep⟩ := geometric_hahn_banach_point_closed
    (polarFibre_convex hβ hβhalf v).closure isClosed_closure hn
  let T : PolarSource → LogIndex →₀ ℝ := fun p => logVector p.1
  let D : PolarSource → ℝ := fun p => ell ((density hβ hβhalf) p.1)
  have hcost : ∀ d : PolarSource →₀ ℝ, (∀ p, 0 ≤ d p) →
      linearCombination ℝ T d = v → s ≤ linearCombination ℝ D d := by
    intro d hd htd
    have he := (hsep (linearCombination ℝ (fun p : PolarSource => (density hβ hβhalf) p.1) d)
      (subset_closure ⟨d,hd,htd,rfl⟩)).le
    have hmap := Finsupp.apply_linearCombination ℝ ell.toLinearMap
      (fun p : PolarSource => (density hβ hβhalf) p.1) d
    change ell (linearCombination ℝ (fun p : PolarSource => (density hβ hβhalf) p.1) d) =
      linearCombination ℝ D d at hmap
    rwa [hmap] at he
  obtain ⟨b,hbv,hb⟩ := support_fibre T D
    (fun j => ⟨coordinateSource j (-1),coordinateSource_trace j (-1)⟩)
    (fun j => ⟨coordinateSource j 1,coordinateSource_trace j 1⟩)
    v s (trace_reachable v) hcost
  have hfull := full_pairing_bound hβ hβhalf b ell hb
  have hsum : linearCombination ℝ (fun f => linearCombination ℝ b (logVector f)) c ≤
      linearCombination ℝ (fun f => ell ((density hβ hβhalf) f)) c := by
    simp only [linearCombination_apply,Finsupp.sum,smul_eq_mul]
    exact Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hfull f) (hc f)
  have hl := Finsupp.apply_linearCombination ℝ (linearCombination ℝ b) logVector c
  have hr := Finsupp.apply_linearCombination ℝ ell.toLinearMap (density hβ hβhalf) c
  change linearCombination ℝ b (linearCombination ℝ logVector c) =
    linearCombination ℝ (fun f => linearCombination ℝ b (logVector f)) c at hl
  change ell (linearCombination ℝ (density hβ hβhalf) c) =
    linearCombination ℝ (fun f => ell ((density hβ hβhalf) f)) c at hr
  rw [← hl,← hr,ht,hρ] at hsum
  linarith

/-- Exact whole integer fibres have the same spectral sub-half-logarithmic L1 closure with or without polar zeros. -/
theorem closure_polarFibre_eq_fullFibre (v : LogIndex →₀ ℝ) :
    closure (polarFibre hβ hβhalf v) = closure (fullFibre hβ hβhalf v) := by
  apply le_antisymm
  · exact closure_mono (polarFibre_subset_fullFibre hβ hβhalf v)
  · exact closure_minimal (fullFibre_subset_closure_polarFibre hβ hβhalf v) isClosed_closure

/-- Every actual finite positive full-source mixture has arbitrary weighted L1-accurate polar
recovery with its whole integer trace fixed exactly. -/
theorem exists_exact_fibre_recovery (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : PolarSource →₀ ℝ, (∀ p, 0 ≤ d p) ∧
      linearCombination ℝ (fun p => logVector p.1) d = linearCombination ℝ logVector c ∧
      ‖linearCombination ℝ (fun p => (density hβ hβhalf) p.1) d-linearCombination ℝ (density hβ hβhalf) c‖ < ε := by
  have hm := fullFibre_subset_closure_polarFibre hβ hβhalf (linearCombination ℝ logVector c)
    (show linearCombination ℝ (density hβ hβhalf) c ∈ fullFibre hβ hβhalf (linearCombination ℝ logVector c) from
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

/-- Recovery preserves every literal raw atom, including the entire zero tail. -/
theorem exists_raw_fibre_recovery (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d : PolarSource →₀ ℝ, (∀ p, 0 ≤ d p) ∧
      (∀ n : ℕ, 2 ≤ n →
        linearCombination ℝ (fun p => atomCoeff p.1.1 n) d =
          linearCombination ℝ (fun f => atomCoeff f.1 n) c) ∧
      ‖linearCombination ℝ (fun p => (density hβ hβhalf) p.1) d-linearCombination ℝ (density hβ hβhalf) c‖ < ε := by
  obtain ⟨d,hd,ht,he⟩ := exists_exact_fibre_recovery hβ hβhalf c hc hε
  refine ⟨d,hd,?_,he⟩
  intro n hn
  have h := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n,hn⟩) ht
  rw [trace_coordinate (fun p : PolarSource => p.1),trace_coordinate (fun f : WeilTestFn => f)] at h
  have hn0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))).ne'
  exact (div_left_inj' hn0).mp h

private theorem fejerFullSource_trace_zero : logVector fejerFullSource = 0 := by
  ext j
  rw [logVector_apply,Finsupp.zero_apply]
  have hj : 2*(17/50 : ℝ) < |Real.log j| := by
    have h2 : Real.log 2 ≤ Real.log j := Real.log_le_log (by norm_num) (by exact_mod_cast j.2)
    have := Real.log_two_gt_d9
    rw [abs_of_nonneg (by linarith)]; linarith
  have hp := weilTest_self_eq_zero (fun u hu => fejerTest_eq_zero hu) hj
  have hm := weilTest_self_eq_zero (fun u hu => fejerTest_eq_zero hu)
    (show 2*(17/50 : ℝ) < |-Real.log j| by rwa [abs_neg])
  change (Zeta23.EF.weilTest fejerTest fejerTest (Real.log j)+
    Zeta23.EF.weilTest fejerTest fejerTest (-Real.log j)).re / Real.sqrt j = 0
  rw [hp,hm]; simp

/-- Actual finite positive polar mixtures recover the literal Fejer density while
remaining exactly integer-null. No energy, aperture or row-count bound is asserted. -/
theorem exists_fejer_null_recovery {ε : ℝ} (hε : 0 < ε) :
    ∃ d : PolarSource →₀ ℝ, (∀ p, 0 ≤ d p) ∧
      (∀ n : ℕ, 2 ≤ n → linearCombination ℝ (fun p => atomCoeff p.1.1 n) d = 0) ∧
      ‖linearCombination ℝ (fun p => (density hβ hβhalf) p.1) d-(density hβ hβhalf) fejerFullSource‖ < ε := by
  classical
  have hc : ∀ f, 0 ≤ (Finsupp.single fejerFullSource (1 : ℝ)) f := by
    intro f; simp only [Finsupp.single_apply]; split_ifs <;> positivity
  obtain ⟨d,hd,ht,he⟩ := exists_exact_fibre_recovery hβ hβhalf (Finsupp.single fejerFullSource 1) hc hε
  simp only [linearCombination_single,one_smul,fejerFullSource_trace_zero] at ht he
  refine ⟨d,hd,?_,he⟩
  intro n hn
  have hj := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n,hn⟩) ht
  rw [trace_coordinate (fun p : PolarSource => p.1),Finsupp.zero_apply] at hj
  have hn0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))).ne'
  exact (div_eq_zero_iff.mp hj).resolve_right hn0

end RHTower.ExposingRayTransfer.SublogFibre
