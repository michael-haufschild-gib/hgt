import GaloisForLFunctions.RHTower.EvenSectorPolarCompletion
import GaloisForLFunctions.RHTower.WeilWorkExposingRayOnePoleFibreDensity

/-!
# Actual even pole-free recovery in every arithmetic energy fibre

Every finite positive full-source mixture admits finite positive even pole-free
recovery with exactly the same whole integer trace and arbitrarily small excess
of the actual pole-plus-archimedean energy. The pole term of each recovery row
vanishes. No RH, source positivity, growth, or recovery premise is required.

Signed even polar coordinate rays give feasibility. A strict fibre cost gap
would supply an arithmetic supporting functional. Automatic EWU completion
makes that functional positive on the original full mixture, a contradiction.
Thus the closed energy epigraphs coincide in every exact arithmetic fibre.
This constructs witnesses; it does not assert nonnegative energy in the blind fibre.
-/

open MeasureTheory Set Finsupp Zeta23
noncomputable section
namespace RHTower.EvenSector
open WeilOneSided SeparatedBump

/-- All integer samples of an actual finite even polar mixture. -/
def polarMixtureTrace : (WeilEvenPolarTestFn →₀ ℝ) →ₗ[ℝ] (LogIndex →₀ ℝ) :=
  linearCombination ℝ (fun f => logVector f.1)

/-- Actual archimedean cost; the pole part vanishes on these rows. -/
def polarMixtureEnergy : (WeilEvenPolarTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
  linearCombination ℝ (fun f => weilArchRe (EF.weilTest f.1.1 f.1.1))

/-- Actual pole-plus-archimedean cost of a finite full-source mixture. -/
def fullMixtureEnergy : (WeilTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
  linearCombination ℝ (fun f => weilArchRe (EF.weilTest f.1 f.1))

private theorem signed_coordinate_mixtures (j : LogIndex) :
    (∃ c : WeilEvenPolarTestFn →₀ ℝ,(∀ f,0≤c f) ∧
      polarMixtureTrace c=Finsupp.single j (-1)) ∧
    (∃ c : WeilEvenPolarTestFn →₀ ℝ,(∀ f,0≤c f) ∧
      polarMixtureTrace c=Finsupp.single j 1) := by
  classical
  have hj : 0<Real.sqrt (j:ℕ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<j.1 by omega))
  let km := 2*(∫ u,oddPolarProfile j u^2)/Real.sqrt j
  let kp := 2*(∫ u,evenPolarProfile j u^2)/Real.sqrt j
  have hm : 0<km := div_pos (mul_pos two_pos (integral_oddPolarProfile_sq_pos j)) hj
  have hp : 0<kp := div_pos (mul_pos two_pos (lt_of_lt_of_le
    (by have := integral_narrowBump_sq_pos 0; have := nodeScale_pos j; positivity)
    (le_integral_evenPolarProfile_sq j))) hj
  constructor
  · refine ⟨Finsupp.single (evenPolarMinusTest j) km⁻¹,?_,?_⟩
    · intro f
      simp only [Finsupp.single_apply]
      split_ifs <;> positivity
    · rw [polarMixtureTrace,linearCombination_single,logVector_evenPolarMinusTest,
        Finsupp.smul_single,smul_eq_mul]
      change Finsupp.single j (km⁻¹*(-km))=Finsupp.single j (-1)
      rw [mul_neg,inv_mul_cancel₀ hm.ne']
  · refine ⟨Finsupp.single (evenPolarNodeTest j) kp⁻¹,?_,?_⟩
    · intro f
      simp only [Finsupp.single_apply]
      split_ifs <;> positivity
    · rw [polarMixtureTrace,linearCombination_single]
      change kp⁻¹ • logVector (evenPolarNode j).1=_
      rw [logVector_evenPolarNode,Finsupp.smul_single,smul_eq_mul]
      change Finsupp.single j (kp⁻¹*kp)=Finsupp.single j 1
      rw [inv_mul_cancel₀ hp.ne']

/-- Every whole arithmetic trace is reached by positive even pole-free mixtures. -/
theorem exists_evenPolar_mixture_trace (v : LogIndex →₀ ℝ) :
    ∃ c : WeilEvenPolarTestFn →₀ ℝ,(∀ f,0≤c f) ∧ polarMixtureTrace c=v := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => exact ⟨0,fun _ => le_rfl,by simp⟩
  | add v w hv hw =>
    obtain ⟨c,hc,ht⟩ := hv
    obtain ⟨d,hd,hu⟩ := hw
    exact ⟨c+d,fun f => add_nonneg (hc f) (hd f),by rw [map_add,ht,hu]⟩
  | single j r =>
    obtain ⟨⟨cm,hm,htm⟩,⟨cp,hp,htp⟩⟩ := signed_coordinate_mixtures j
    by_cases hr : 0≤r
    · exact ⟨r • cp,fun f => mul_nonneg hr (hp f),by
        rw [map_smul,htp,Finsupp.smul_single,smul_eq_mul,mul_one]⟩
    · refine ⟨(-r) • cm,fun f => mul_nonneg (by linarith) (hm f),?_⟩
      rw [map_smul,htm,Finsupp.smul_single,smul_eq_mul]
      congr 1
      ring

private def PositivePolarMixture := {c : WeilEvenPolarTestFn →₀ ℝ // ∀ f,0≤c f}

private theorem flatten_nonneg (d : PositivePolarMixture →₀ ℝ) (hd : ∀ p,0≤d p) (f : WeilEvenPolarTestFn) :
    0 ≤ (linearCombination ℝ (fun p : PositivePolarMixture => p.1) d) f := by
  classical
  simp only [linearCombination_apply,Finsupp.sum,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (hd p) (p.2 f)

/-- Actual finite positive even pole-free recovery. All arithmetic coordinates
are exact; the only tolerance is in the actual archimedean energy. -/
theorem exists_evenPolar_exact_fibre_recovery (c : WeilTestFn →₀ ℝ) (hc : ∀ f,0≤c f)
    {ε : ℝ} (hε : 0<ε) :
    ∃ d : WeilEvenPolarTestFn →₀ ℝ,(∀ f,0≤d f) ∧
      polarMixtureTrace d=linearCombination ℝ logVector c ∧
      polarMixtureEnergy d<fullMixtureEnergy c+ε := by
  classical
  by_contra hn
  let v := linearCombination ℝ logVector c
  let r := fullMixtureEnergy c+ε
  have hlower (d : WeilEvenPolarTestFn →₀ ℝ) (hd : ∀ f,0≤d f)
      (ht : polarMixtureTrace d=v) : r≤polarMixtureEnergy d := by
    by_contra hh
    exact hn ⟨d,hd,ht,lt_of_not_ge hh⟩
  let T : PositivePolarMixture → LogIndex →₀ ℝ := fun p => polarMixtureTrace p.1
  let D : PositivePolarMixture → ℝ := fun p => polarMixtureEnergy p.1
  have hreach (w : LogIndex →₀ ℝ) : ∃ p : PositivePolarMixture,T p=w := by
    obtain ⟨d,hd,ht⟩ := exists_evenPolar_mixture_trace w
    exact ⟨⟨d,hd⟩,ht⟩
  have hex : ∃ d : PositivePolarMixture →₀ ℝ,(∀ p,0≤d p) ∧ linearCombination ℝ T d=v := by
    obtain ⟨p,hp⟩ := hreach v
    exact ⟨Finsupp.single p 1,fun q => by simp only [Finsupp.single_apply]; split_ifs <;> positivity,
      by simp [hp]⟩
  have hcost (d : PositivePolarMixture →₀ ℝ) (hd : ∀ p,0≤d p)
      (ht : linearCombination ℝ T d=v) : r≤linearCombination ℝ D d := by
    have hT := Finsupp.apply_linearCombination ℝ polarMixtureTrace
      (fun p : PositivePolarMixture => p.1) d
    have hD := Finsupp.apply_linearCombination ℝ polarMixtureEnergy
      (fun p : PositivePolarMixture => p.1) d
    have htrace : polarMixtureTrace (linearCombination ℝ (fun p : PositivePolarMixture => p.1) d)=v :=
      hT.trans ht
    have hh := hlower _ (flatten_nonneg d hd) htrace
    rwa [hD] at hh
  obtain ⟨b,hbv,hb⟩ := ExposingRayTransfer.OnePoleFibre.support_fibre T D
    (fun j => hreach (Finsupp.single j (-1))) (fun j => hreach (Finsupp.single j 1))
    v r hex hcost
  have hrow (f : WeilEvenPolarTestFn) :
      linearCombination ℝ b (logVector f.1)≤weilArchRe (EF.weilTest f.1.1 f.1.1) := by
    let p : PositivePolarMixture := ⟨Finsupp.single f 1,
      fun g => by simp only [Finsupp.single_apply]; split_ifs <;> positivity⟩
    simpa [T,D,p,polarMixtureTrace,polarMixtureEnergy] using hb p
  let lam : ℕ → ℝ := fun n => if hn : 2≤n then b ⟨n,hn⟩ else 0
  have hlam : (fun j : LogIndex => lam j)=b := by
    funext j
    simp [lam,j.2]
  have hpf : WeilPositiveEvenPolar lam := by
    intro f hf hfc he hp
    have hh := hrow ⟨⟨f,hf,hfc⟩,he,hp⟩
    rw [re_weilFullFunctional_eq lam ⟨f,hf,hfc⟩,hlam]
    exact sub_nonneg.mpr hh
  have hfull := weilPositiveFull_of_weilPositiveEvenPolar hpf
  have hsource (f : WeilTestFn) :
      linearCombination ℝ b (logVector f)≤weilArchRe (EF.weilTest f.1 f.1) := by
    have hh := hfull f.1 f.2.1 f.2.2
    rw [re_weilFullFunctional_eq lam f,hlam] at hh
    exact sub_nonneg.mp hh
  have hsum : linearCombination ℝ (fun f => linearCombination ℝ b (logVector f)) c≤
      fullMixtureEnergy c := by
    simp only [fullMixtureEnergy,linearCombination_apply,Finsupp.sum,smul_eq_mul]
    exact Finset.sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hsource f) (hc f)
  have he := Finsupp.apply_linearCombination ℝ (linearCombination ℝ b) logVector c
  simp only [Function.comp_def] at he
  rw [← he] at hsum
  change r≤linearCombination ℝ b v at hbv
  dsimp [r,v] at hbv
  linarith

/-- The full-source energy epigraph in one exact arithmetic fibre. -/
def fullEnergyEpigraph (v : LogIndex →₀ ℝ) : Set ℝ :=
  {r | ∃ c : WeilTestFn →₀ ℝ,(∀ f,0≤c f) ∧
    linearCombination ℝ logVector c=v ∧ fullMixtureEnergy c≤r}

/-- The even pole-free energy epigraph in that same whole arithmetic fibre. -/
def evenPolarEnergyEpigraph (v : LogIndex →₀ ℝ) : Set ℝ :=
  {r | ∃ d : WeilEvenPolarTestFn →₀ ℝ,(∀ f,0≤d f) ∧
    polarMixtureTrace d=v ∧ polarMixtureEnergy d≤r}

/-- **EWU energy-fibre completion.** Imposing both evenness and literal pole
zeros preserves every closed arithmetic energy epigraph. No positivity
hypothesis on either cone is used. -/
theorem evenPolar_energy_fibre_closure_eq (v : LogIndex →₀ ℝ) :
    closure (evenPolarEnergyEpigraph v)=closure (fullEnergyEpigraph v) := by
  apply le_antisymm
  · apply closure_mono
    intro r hr
    obtain ⟨d,hd,ht,he⟩ := hr
    refine ⟨d.mapDomain Subtype.val,Finsupp.mapDomain_nonneg hd,?_,?_⟩
    · rw [Finsupp.linearCombination_mapDomain]
      exact ht
    · change linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1))
        (d.mapDomain Subtype.val)≤r
      rw [Finsupp.linearCombination_mapDomain]
      exact he
  · apply closure_minimal _ isClosed_closure
    intro r hr
    obtain ⟨c,hc,ht,he⟩ := hr
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨d,hd,htrace,henergy⟩ := exists_evenPolar_exact_fibre_recovery c hc (half_pos hε)
    refine ⟨r+ε/2,⟨d,hd,htrace.trans ht,by linarith⟩,?_⟩
    rw [Real.dist_eq,show r-(r+ε/2)=-(ε/2) by ring,abs_neg,abs_of_pos (half_pos hε)]
    linarith

end RHTower.EvenSector
