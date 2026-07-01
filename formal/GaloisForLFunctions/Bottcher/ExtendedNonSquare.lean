/-
# Generalized deep non-square: abstract radicand `F` on `Ext` (no crude-escape pin)

`BottcherIterateNonSquare.bottcherIterateGerm_not_isSquare` proves the non-square clause of
`Q62RadicalReduction.q62_disconnected_of_radical_data` for the radicand `bottcherCoord∘f^[k]`,
which pins the deep domain to `{z | f^[k] z ∈ escapeOpen}` — satisfiable only when the critical
Green level `G_c(0)` clears the crude escape threshold (the `‖c‖`-large regime).  The genuine
Branner–Hubbard loops live at Green level `< G_c(0)/2^k` with image level in `(G_c(0), 2·G_c(0))`,
outside the crude region for general `c ∉ M`.

This file removes the pin: the radicand is an **arbitrary analytic nonvanishing `F` on `Ext`**
(the continued `φ_c^{2^k}` supplied by the tower construction), the loop avoidance is in the
**domain** (`γ θ ∉ T`, matching level-parametrized loop families), and the non-square in
`meroField Ext` follows from a closed `C¹` loop with **odd** `logDeriv F`-period.  The radical
relation and `φ_{c₂}`-compatibility clauses become germ-restriction hypotheses.  Assembled into
`q62_disconnected_of_towerData` (one tower + `φ₂` transcendence) and
`q62_disconnected_of_towerData_two` (two towers, transcendence internal).  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.Q62RadicalReduction
import GaloisForLFunctions.Bottcher.NonSquareWinding
import GaloisForLFunctions.Bottcher.ZeroSet

open Complex Set Filter

namespace Bottcher

/-- **No analytic square root of an abstract nonvanishing `F` near a closed odd-period loop.**
If a closed `C¹` loop `γ` lies in an open `A` where `F` is analytic and nonvanishing, and the
period `∮_γ d log F` is an odd multiple of `2πi`, then `F` has no analytic square root on `A`.
Abstract form of `no_analytic_sqrt_bottcherIterate_of_oddPeriod`: the radicand is any `F`, not
`bottcherCoord∘f^[k]`. -/
theorem no_analytic_sqrt_of_oddPeriod {F : ℂ → ℂ} {m : ℤ}
    {A : Set ℂ} (hAo : IsOpen A) (hFan : AnalyticOnNhd ℂ F A) (hFne : ∀ z ∈ A, F z ≠ 0)
    {γ γ' : ℝ → ℂ} (hγA : ∀ θ : ℝ, γ θ ∈ A)
    (hγcont : Continuous γ) (hγ'cont : Continuous γ')
    (hdγ : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ)
    (hγclosed : γ (2 * Real.pi) = γ 0)
    (hperiod : (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))
    (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h A) :
    ¬ Set.EqOn (fun z => h z ^ 2) F A := by
  have hΦcont : Continuous (fun t => logDeriv F (γ t) * γ' t) := by
    have hlogcont : ContinuousOn (logDeriv F) A :=
      (hFan.deriv).continuousOn.div hFan.continuousOn (fun z hz => hFne z hz)
    exact (hlogcont.comp_continuous hγcont hγA).mul hγ'cont
  set La : ℝ → ℂ := fun u => ∫ t in (0:ℝ)..u, logDeriv F (γ t) * γ' t with hLadef
  have hLa : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      HasDerivAt La (logDeriv F (γ θ) * γ' θ) θ := fun θ _ =>
    intervalIntegral.integral_hasDerivAt_right (hΦcont.intervalIntegrable 0 θ)
      hΦcont.stronglyMeasurable.stronglyMeasurableAtFilter hΦcont.continuousAt
  have hperiodLa : La (2 * Real.pi) - La 0
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1) := by
    have h0 : La 0 = 0 := by simp [hLadef]
    rw [h0, sub_zero,
      show La (2 * Real.pi) = ∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ from rfl]
    exact hperiod
  exact not_eqOn_sq_of_odd_period hAo hFne (fun θ _ => hγA θ) hγclosed hdγ hLa hperiodLa h hh

/-- A germ in `analyticSubring U` is `0` iff its representative vanishes on `U`. -/
private theorem germ_eq_zero_iff_eqOn {U : Set ℂ} {f : ℂ → ℂ} :
    (Filter.Germ.coeRingHom (𝓟 U) f = (0 : Filter.Germ (𝓟 U) ℂ)) ↔ Set.EqOn f 0 U := by
  rw [show Filter.Germ.coeRingHom (𝓟 U) f = (↑f : Filter.Germ (𝓟 U) ℂ) from rfl,
    ← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  exact ⟨fun h z hz => Filter.eventually_principal.mp h z hz,
    fun h => Filter.eventually_principal.mpr (fun z hz => h hz)⟩

/-- **Abstract germ non-square from odd loop periods.**  An analytic nonvanishing `F` on an open
connected `Ext`, carrying — for every countable `T` — a closed `C¹` loop in `Ext ∖ T` with **odd**
`logDeriv F`-period, is not a square in `meroField Ext`.  Abstract form of
`bottcherIterateGerm_not_isSquare`: the avoidance is in the domain (the loop dodges the countable
zero set of the candidate root's numerator/denominator directly), so level-parametrized loop
families discharge it.  This is the non-square clause of
`q62_disconnected_of_radical_data` with the radicand freed from the crude escape region. -/
theorem analyticGerm_not_isSquare {Ext : Set ℂ}
    (hExto : IsOpen Ext) (hExtc : IsConnected Ext)
    {F : ℂ → ℂ} (hFan : AnalyticOnNhd ℂ F Ext) (hFne : ∀ z ∈ Ext, F z ≠ 0)
    (hloops : ∀ T : Set ℂ, T.Countable →
      ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
        (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
        (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
        γ (2 * Real.pi) = γ 0 ∧
        (∀ θ : ℝ, γ θ ∉ T) ∧
        (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))
    (a : analyticSubring Ext)
    (hae : (Filter.Germ.coeRingHom (𝓟 Ext) F) = (a : Filter.Germ (𝓟 Ext) ℂ)) :
    haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
    ∀ b : meroField Ext,
      b ^ 2 ≠ algebraMap (analyticSubring Ext) (meroField Ext) a := by
  haveI hdom := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
  intro b hbsq
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := analyticSubring Ext) b
  have hqunit : IsUnit (algebraMap (analyticSubring Ext) (meroField Ext) q) :=
    IsLocalization.map_units (meroField Ext) ⟨q, hq⟩
  have hqne : algebraMap (analyticSubring Ext) (meroField Ext) q ≠ 0 := hqunit.ne_zero
  have hq0 : q ≠ 0 := fun h => hqne (by rw [h, map_zero])
  rw [← hpq, div_pow, div_eq_iff (pow_ne_zero 2 hqne)] at hbsq
  simp only [← map_pow, ← map_mul] at hbsq
  have hpaq : p ^ 2 = a * q ^ 2 :=
    IsFractionRing.injective (analyticSubring Ext) (meroField Ext) hbsq
  have ha0 : a ≠ 0 := by
    intro h
    have hz0 : (Filter.Germ.coeRingHom (𝓟 Ext) F) = (0 : Filter.Germ (𝓟 Ext) ℂ) := by
      rw [hae, h, ZeroMemClass.coe_zero]
    rw [germ_eq_zero_iff_eqOn] at hz0
    exact hFne _ hExtc.nonempty.choose_spec (hz0 hExtc.nonempty.choose_spec)
  have hp0 : p ≠ 0 := by
    intro h; rw [h] at hpaq
    exact (mul_ne_zero ha0 (pow_ne_zero 2 hq0)) (by rw [← hpaq]; ring)
  obtain ⟨fp, hfp, hfpe⟩ := p.2
  obtain ⟨fq, hfq, hfqe⟩ := q.2
  have hval : (p : Filter.Germ (𝓟 Ext) ℂ) ^ 2
      = (a : Filter.Germ (𝓟 Ext) ℂ) * (q : Filter.Germ (𝓟 Ext) ℂ) ^ 2 := by
    have h := congrArg (fun x : analyticSubring Ext => (x : Filter.Germ (𝓟 Ext) ℂ)) hpaq
    simpa using h
  rw [← hae, ← hfpe, ← hfqe, ← map_pow, ← map_pow, ← map_mul] at hval
  have hEqOn : ∀ z ∈ Ext, fp z ^ 2 = F z * fq z ^ 2 := by
    have hcoeeq : ((fp ^ 2 : ℂ → ℂ) : Filter.Germ (𝓟 Ext) ℂ)
        = ((F * fq ^ 2 : ℂ → ℂ) : Filter.Germ (𝓟 Ext) ℂ) := hval
    rw [Filter.Germ.coe_eq] at hcoeeq
    intro z hz
    have := Filter.eventually_principal.mp hcoeeq z hz
    simpa [Pi.pow_apply, Pi.mul_apply] using this
  have hpq0 : p * q ≠ 0 := mul_ne_zero hp0 hq0
  have hgerm_pq :
      (Filter.Germ.coeRingHom (𝓟 Ext) (fun z => fp z * fq z)) ≠ (0 : Filter.Germ (𝓟 Ext) ℂ) := by
    have hcoe : (Filter.Germ.coeRingHom (𝓟 Ext) (fun z => fp z * fq z))
        = ((p * q : analyticSubring Ext) : Filter.Germ (𝓟 Ext) ℂ) := by
      rw [show (fun z => fp z * fq z) = (fun z => fp z) * (fun z => fq z) from rfl, map_mul,
        hfpe, hfqe, MulMemClass.coe_mul]
    rw [hcoe]; intro h; apply hpq0; apply Subtype.ext; rw [ZeroMemClass.coe_zero]; exact h
  obtain ⟨w₀, hw₀U, hw₀ne⟩ : ∃ z ∈ Ext, fp z * fq z ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hgerm_pq (germ_eq_zero_iff_eqOn.mpr (fun z hz => by simp [hcon z hz]))
  have hZcount : {z ∈ Ext | fp z * fq z = 0}.Countable :=
    analyticOnNhd_zeros_countable (hfp.mul hfq) hExtc.isPreconnected hw₀U hw₀ne
  obtain ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, hperiod⟩ :=
    hloops _ hZcount
  set A : Set ℂ := {z | z ∈ Ext ∧ fp z ≠ 0 ∧ fq z ≠ 0} with hAdef
  have hAo : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨hzU, hzfp, hzfq⟩
    have hUnhds : Ext ∈ nhds z := hExto.mem_nhds hzU
    have h1 : {w | fp w ≠ 0} ∈ nhds z :=
      (hfp z hzU).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hzfp)
    have h2 : {w | fq w ≠ 0} ∈ nhds z :=
      (hfq z hzU).continuousAt.preimage_mem_nhds (isOpen_ne.mem_nhds hzfq)
    filter_upwards [hUnhds, h1, h2] with w hw1 hw2 hw3
    exact ⟨hw1, hw2, hw3⟩
  have hγA : ∀ θ : ℝ, γ θ ∈ A := by
    intro θ
    refine ⟨hγExt θ, ?_, ?_⟩
    · intro h0; exact havoid θ ⟨hγExt θ, by rw [h0]; ring⟩
    · intro h0; exact havoid θ ⟨hγExt θ, by rw [h0]; ring⟩
  have hFanA : AnalyticOnNhd ℂ F A := hFan.mono (fun z hz => hz.1)
  have hFneA : ∀ z ∈ A, F z ≠ 0 := fun z hz => hFne z hz.1
  have hhdiv : AnalyticOnNhd ℂ (fun z => fp z / fq z) A :=
    (hfp.mono (fun z hz => hz.1)).div (hfq.mono (fun z hz => hz.1)) (fun z hz => hz.2.2)
  have hsqA : Set.EqOn (fun z => (fp z / fq z) ^ 2) F A := by
    intro z hz
    have hfqz : fq z ≠ 0 := hz.2.2
    have heq := hEqOn z hz.1
    show (fp z / fq z) ^ 2 = F z
    rw [div_pow, heq, mul_div_assoc, div_self (pow_ne_zero 2 hfqz), mul_one]
  exact no_analytic_sqrt_of_oddPeriod hAo hFanA hFneA hγA hγcont hγ'cont hdγ hγclosed
    hperiod _ hhdiv hsqA

end Bottcher

namespace Bottcher

/-- **[Radical relation, restriction form]** If the deep radicand germ `aExt` restricts on `U` to
`a₁^{2^k}`, then `(algebraMap a₁)^{2^k} = restrictMeroHom (algebraMap aExt)` — the radical clause
of `q62_disconnected_of_radical_data` with `i = restrictMeroHom`, freed from the pointwise
`bottcherCoord∘f^[k]` formula. -/
theorem radical_relation_restrict {U Ext : Set ℂ} (k : ℕ) (hUExt : U ⊆ Ext)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hExto : IsOpen Ext) (hExtc : IsPreconnected Ext) (hExtne : Ext.Nonempty)
    (a₁ : analyticSubring U) (aExt : analyticSubring Ext)
    (hrad : restrictAnalytic hUExt aExt = a₁ ^ (2 ^ k)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := isDomain_analyticSubring Ext hExto hExtc hExtne
    (algebraMap (analyticSubring U) (meroField U) a₁) ^ (2 ^ k)
      = restrictMeroHom hUExt hExto hExtc hExtne hUo hUc hUne
          (algebraMap (analyticSubring Ext) (meroField Ext) aExt) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring Ext hExto hExtc hExtne
  rw [restrictMeroHom_algebraMap, hrad, map_pow]

/-- **[q62 disconnected from tower data]** The deep-data close with the radicand freed from the
crude escape region: per depth `d`, a connected `Ext ⊇ U` carrying an analytic nonvanishing `F`
(the continued `φ_{c₁}^{2^k}`) whose germ `aExt` restricts on `U` to `a₁^{2^k}`, a `φ_{c₂}` germ
`GBExt` restricting to `a₂`, and — for every countable `T` — a closed `C¹` loop in `Ext ∖ T` with
odd `logDeriv F`-period.  Assembles `q62_disconnected_of_radical_data` with `B = meroField Ext`,
`i = restrictMeroHom`.  This is the interface the Branner–Hubbard tower construction discharges
for general `c₁ ∉ M` (no `‖c₁‖`-large hypothesis). -/
theorem q62_disconnected_of_towerData {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (a₁ a₂ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hGtr : haveI := isDomain_analyticSubring U hUo hUc hUne
            haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
            Transcendental (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₂))
    (towerdata : ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt GBExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = a₁ ^ (2 ^ k) ∧
        restrictAnalytic hUExt GBExt = a₂ ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI algU := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply q62_disconnected_of_radical_data hUo hUc hUne a₁ a₂ hF hGtr
  intro d
  obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, GBExt, k, hk1, hdk,
    hFan, hFne, hae, hrad, hGB, hloops⟩ := towerdata d
  haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
  letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
  let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
    { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
      commutes' := fun r => RingHom.congr_fun
        (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
          hUo hUc hUne hUinf) r }
  refine ⟨meroField Ext, inferInstance, inferInstance, i,
    algebraMap (analyticSubring Ext) (meroField Ext) aExt,
    algebraMap (analyticSubring Ext) (meroField Ext) GBExt, k,
    hk1, hdk, ?_, ?_, ?_⟩
  · exact analyticGerm_not_isSquare hExto hExtc hFan hFne hloops aExt hae
  · exact radical_relation_restrict k hUExt hUo hUc hUne hExto hExtc.isPreconnected
      hExtc.nonempty a₁ aExt hrad
  · show restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
        (algebraMap (analyticSubring Ext) (meroField Ext) GBExt)
      = algebraMap (analyticSubring U) (meroField U) a₂
    rw [restrictMeroHom_algebraMap, hGB]

/-- **[q62 disconnected from two towers]** As `q62_disconnected_of_towerData`, but the `φ_{c₂}`
transcendence input is replaced by `c₂`'s own single-coordinate tower (radicand `F₂`, its own odd
loops, no `GB` clause) — the transcendence is then internal (Kummer).  The pair close for two
general disconnected parameters, given each coordinate's tower plus the `φ₂`-compatibility germ on
the first tower's domain. -/
theorem q62_disconnected_of_towerData_two {U : Set ℂ}
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (a₁ a₂ : analyticSubring U)
    (hF : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₁ ≠ 0)
    (hG : haveI := isDomain_analyticSubring U hUo hUc hUne
          algebraMap (analyticSubring U) (meroField U) a₂ ≠ 0)
    (towerdataF : ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt GBExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = a₁ ^ (2 ^ k) ∧
        restrictAnalytic hUExt GBExt = a₂ ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1)))
    (towerdataG : ∀ d : ℕ, ∃ (Ext : Set ℂ)
        (_hExto : IsOpen Ext) (_hExtc : IsConnected Ext) (_hExtinf : Ext.Infinite)
        (hUExt : U ⊆ Ext) (F : ℂ → ℂ) (aExt : analyticSubring Ext) (k : ℕ),
        1 ≤ k ∧ d < 2 ^ k ∧
        AnalyticOnNhd ℂ F Ext ∧ (∀ z ∈ Ext, F z ≠ 0) ∧
        (Filter.Germ.coeRingHom (𝓟 Ext) F) = (aExt : Filter.Germ (𝓟 Ext) ℂ) ∧
        restrictAnalytic hUExt aExt = a₂ ^ (2 ^ k) ∧
        (∀ T : Set ℂ, T.Countable →
          ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
            (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
            (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
            γ (2 * Real.pi) = γ 0 ∧
            (∀ θ : ℝ, γ θ ∉ T) ∧
            (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv F (γ θ) * γ' θ)
              = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
    NoRelation (RatFunc ℂ) (algebraMap (analyticSubring U) (meroField U) a₁)
      (algebraMap (analyticSubring U) (meroField U) a₂) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  letI algU := (ratfuncToMero U hUo hUc hUne hUinf).toAlgebra
  apply q62_disconnected_of_two_radical_data hUo hUc hUne a₁ a₂ hF hG
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, GBExt, k, hk1, hdk,
      hFan, hFne, hae, hrad, hGB, hloops⟩ := towerdataF d
    haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
    letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
    let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
      { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
        commutes' := fun r => RingHom.congr_fun
          (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
            hUo hUc hUne hUinf) r }
    refine ⟨meroField Ext, inferInstance, inferInstance, i,
      algebraMap (analyticSubring Ext) (meroField Ext) aExt,
      algebraMap (analyticSubring Ext) (meroField Ext) GBExt, k,
      hk1, hdk, ?_, ?_, ?_⟩
    · exact analyticGerm_not_isSquare hExto hExtc hFan hFne hloops aExt hae
    · exact radical_relation_restrict k hUExt hUo hUc hUne hExto hExtc.isPreconnected
        hExtc.nonempty a₁ aExt hrad
    · show restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne
          (algebraMap (analyticSubring Ext) (meroField Ext) GBExt)
        = algebraMap (analyticSubring U) (meroField U) a₂
      rw [restrictMeroHom_algebraMap, hGB]
  · intro d
    obtain ⟨Ext, hExto, hExtc, hExtinf, hUExt, F, aExt, k, hk1, hdk,
      hFan, hFne, hae, hrad, hloops⟩ := towerdataG d
    haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
    letI algExt := (ratfuncToMero Ext hExto hExtc.isPreconnected hExtc.nonempty hExtinf).toAlgebra
    let i : meroField Ext →ₐ[RatFunc ℂ] meroField U :=
      { restrictMeroHom hUExt hExto hExtc.isPreconnected hExtc.nonempty hUo hUc hUne with
        commutes' := fun r => RingHom.congr_fun
          (restrictMeroHom_ratfuncToMero hUExt hExto hExtc.isPreconnected hExtc.nonempty hExtinf
            hUo hUc hUne hUinf) r }
    refine ⟨meroField Ext, inferInstance, inferInstance, i,
      algebraMap (analyticSubring Ext) (meroField Ext) aExt, k,
      hk1, hdk, ?_, ?_⟩
    · exact analyticGerm_not_isSquare hExto hExtc hFan hFne hloops aExt hae
    · exact radical_relation_restrict k hUExt hUo hUc hUne hExto hExtc.isPreconnected
        hExtc.nonempty a₂ aExt hrad

end Bottcher
