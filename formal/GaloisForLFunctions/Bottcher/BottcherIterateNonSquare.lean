/-
# Deep-level (k ≥ 1) non-square of `bottcherCoord∘f^[k]` from the closed deep-loop odd period

`Q62RadicalReduction.q62_disconnected_of_radical_data` reduces `hDisc` to: for each depth, the
radicand `a = φ_{c₁}^{2^k}` (`k ≥ 1`) is **not a square** in the base field.  Over the escape region
`a = bottcherCoord∘f^[k] = bottcherCoord^{2^k}` is a perfect square — so the non-square only lives on
a *deeper* domain `Ext`, carrying a **closed** loop `γ` (one turn around a depth-`k` lobe) on which
the multivalued `bottcherCoord` has the fractional period `2πi/2^k`, hence `bottcherCoord∘f^[k] =
bottcherCoord^{2^k}` has the **odd** period `2πi`.  (Note: `γ` is closed but its `f^[k]`-image winds
*once* around `K_c`; the exact base circle `C(0,R)` has *no* closed winding-one lift for `k ≥ 1` — the
dyadic monodromy moves the sheet — so the period is taken over the genuine closed deep loop, not a
circle lift.)

Built here, axiom-clean, via the general-loop winding obstruction
`NonSquareWinding.not_eqOn_sq_of_odd_period`:

* `pathInt_logDeriv_iterate_eq_image` — the chain-rule reduction `∮_γ d log(bottcherCoord∘f^[k]) =
  ∮_{f^[k]∘γ} d log bottcherCoord` (no winding assumption);
* `no_analytic_sqrt_bottcherIterate_of_oddPeriod` — a closed deep loop with radicand period an odd
  multiple of `2πi` forbids any analytic square root of `bottcherCoord∘f^[k]`;
* `bottcherIterateGerm_not_isSquare` — hence `bottcherCoord∘f^[k]` is not a square in `meroField(Ext)`,
  reducing `hDisc` to the single geometric input: the closed depth-`k` lift loop (with its odd radicand
  period and avoidance of the denominator zeros).
-/
import GaloisForLFunctions.Bottcher.LiftPeriod
import GaloisForLFunctions.Bottcher.NonSquareWinding
import GaloisForLFunctions.Bottcher.ZeroSet

open Complex Set Filter

namespace Bottcher

/-- **[Chain-rule period reduction] `d log(bottcherCoord∘f^[k])` over `γ` is `d log bottcherCoord`
over the image loop `σ = f^[k]∘γ`.**  Pointwise by `logDeriv_comp` and the iterate chain rule
`(f^[k])'(γθ) = ∏_{j<k} 2·f^[j](γθ)`, where `σ'θ = (f^[k])'(γθ)·γ'θ` is the velocity of the image
loop.  No winding/closure hypothesis — purely the change of variables collapsing the `k`-fold
dynamics onto its image contour.  The base-loop period (`circleIntegral_logDeriv_bottcher` or the
winding-`1` value `2πi`) then supplies the radicand's period. -/
theorem pathInt_logDeriv_iterate_eq_image {c : ℂ} (k : ℕ) {γ γ' σ' : ℝ → ℂ}
    (hAesc : ∀ θ : ℝ, (quadratic c)^[k] (γ θ) ∈ escapeOpen c)
    (hvel : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
        (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ)) * γ' θ = σ' θ) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun z => bottcherCoord c ((quadratic c)^[k] z)) (γ θ) * γ' θ)
      = ∫ θ in (0:ℝ)..(2 * Real.pi),
          logDeriv (bottcherCoord c) ((quadratic c)^[k] (γ θ)) * σ' θ := by
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hesc : (quadratic c)^[k] (γ θ) ∈ escapeOpen c := hAesc θ
  have hbcdiff : DifferentiableAt ℂ (bottcherCoord c) ((quadratic c)^[k] (γ θ)) :=
    (differentiableOn_bottcherCoord c).differentiableAt ((isOpen_escapeOpen c).mem_nhds hesc)
  have hitdiff : DifferentiableAt ℂ (fun z => (quadratic c)^[k] z) (γ θ) :=
    (hasDerivAt_quadratic_iterate c (γ θ) k).differentiableAt
  have hcomp : logDeriv (fun z => bottcherCoord c ((quadratic c)^[k] z)) (γ θ)
      = logDeriv (bottcherCoord c) ((quadratic c)^[k] (γ θ))
        * deriv (fun z => (quadratic c)^[k] z) (γ θ) :=
    logDeriv_comp hbcdiff hitdiff
  have hderiv_it : deriv (fun z => (quadratic c)^[k] z) (γ θ)
      = ∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ) :=
    (hasDerivAt_quadratic_iterate c (γ θ) k).deriv
  show logDeriv (fun z => bottcherCoord c ((quadratic c)^[k] z)) (γ θ) * γ' θ
      = logDeriv (bottcherCoord c) ((quadratic c)^[k] (γ θ)) * σ' θ
  rw [hcomp, hderiv_it, mul_assoc, hvel θ hθ]

/-- **[Deep non-square] No analytic square root of `bottcherCoord∘f^[k]` near a closed odd-period
loop.**  The `k ≥ 1` analytic non-square that `q62_disconnected_of_radical_data` consumes: if a
*closed* `C¹` loop `γ` lies in an open `A` on which `f^[k]` lands in the escape set, and the radicand
`a = bottcherCoord c ∘ f^[k]` has period an **odd** multiple `2πi·(2m+1)` along `γ`, then `a` has no
analytic square root on `A`.  The running integral of `d log a` along `γ` is an antiderivative with
that odd total change, so `not_eqOn_sq_of_odd_period` refutes any analytic root.  This is the genuine
deep-loop analogue of `SquareFree.no_analytic_sqrt_bottcher_circle` (`k = 0`); the closed loop carries
`bottcherCoord`'s fractional period `2πi/2^k`, so `a = bottcherCoord^{2^k}` carries the odd `2πi`. -/
theorem no_analytic_sqrt_bottcherIterate_of_oddPeriod {c : ℂ} (k : ℕ) {m : ℤ}
    {A : Set ℂ} (hAo : IsOpen A) (hAesc : ∀ z ∈ A, (quadratic c)^[k] z ∈ escapeOpen c)
    {γ γ' : ℝ → ℂ} (hγA : ∀ θ : ℝ, γ θ ∈ A)
    (hγcont : Continuous γ) (hγ'cont : Continuous γ')
    (hdγ : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ)
    (hγclosed : γ (2 * Real.pi) = γ 0)
    (hperiod : (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun z => bottcherCoord c ((quadratic c)^[k] z)) (γ θ) * γ' θ)
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))
    (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h A) :
    ¬ Set.EqOn (fun z => h z ^ 2)
        (fun z => bottcherCoord c ((quadratic c)^[k] z)) A := by
  set a : ℂ → ℂ := fun z => bottcherCoord c ((quadratic c)^[k] z) with hadef
  have ha_an : AnalyticOnNhd ℂ a A := by
    intro z hz
    have h1 : AnalyticAt ℂ (bottcherCoord c) ((quadratic c)^[k] z) :=
      ((differentiableOn_bottcherCoord c).analyticOnNhd (isOpen_escapeOpen c)) _ (hAesc z hz)
    have h2 : AnalyticAt ℂ (fun w => (quadratic c)^[k] w) z :=
      (analyticOnNhd_quadratic_iterate c k) z (Set.mem_univ _)
    exact h1.comp h2
  have ha_ne : ∀ z ∈ A, a z ≠ 0 := fun z _ => bottcherCoord_ne_zero c _
  have hΦcont : Continuous (fun t => logDeriv a (γ t) * γ' t) := by
    have hlogcont : ContinuousOn (logDeriv a) A :=
      (ha_an.deriv).continuousOn.div ha_an.continuousOn (fun z hz => ha_ne z hz)
    exact (hlogcont.comp_continuous hγcont hγA).mul hγ'cont
  set La : ℝ → ℂ := fun u => ∫ t in (0:ℝ)..u, logDeriv a (γ t) * γ' t with hLadef
  have hLa : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi),
      HasDerivAt La (logDeriv a (γ θ) * γ' θ) θ := fun θ _ =>
    intervalIntegral.integral_hasDerivAt_right (hΦcont.intervalIntegrable 0 θ)
      hΦcont.stronglyMeasurable.stronglyMeasurableAtFilter hΦcont.continuousAt
  have hperiodLa : La (2 * Real.pi) - La 0
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1) := by
    have h0 : La 0 = 0 := by simp [hLadef]
    rw [h0, sub_zero,
      show La (2 * Real.pi) = ∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv a (γ θ) * γ' θ from rfl]
    exact hperiod
  exact not_eqOn_sq_of_odd_period hAo ha_ne (fun θ _ => hγA θ) hγclosed hdγ hLa hperiodLa h hh

/-- A germ in `analyticSubring U` is `0` iff its representative vanishes on `U`. -/
private theorem germ_eq_zero_iff_eqOn_it {U : Set ℂ} {f : ℂ → ℂ} :
    (Filter.Germ.coeRingHom (𝓟 U) f = (0 : Filter.Germ (𝓟 U) ℂ)) ↔ Set.EqOn f 0 U := by
  rw [show Filter.Germ.coeRingHom (𝓟 U) f = (↑f : Filter.Germ (𝓟 U) ℂ) from rfl,
    ← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  exact ⟨fun h z hz => Filter.eventually_principal.mp h z hz,
    fun h => Filter.eventually_principal.mpr (fun z hz => h hz)⟩

/-- **[Deep meroField non-square] `bottcherCoord∘f^[k]` is not a square in `meroField(Ext)`.**  The
field-level non-square that `Q62RadicalReduction.q62_disconnected_of_radical_data` consumes at depth
`k ≥ 1`, for a deep base domain `Ext` (where `f^[k]` lands in the escape set, so the radicand is a
single-valued analytic germ).  Mirrors `SquareFree.bottcherGerm_not_isSquare` (the `k = 0` circle
case): clear denominators on `b = p/q` to `fp² = (bottcherCoord∘f^[k])·fq²`; the zeros of `fp·fq` are
countable, and the lone geometric input — a **closed** loop `γ` in `Ext` avoiding those zeros (its
`f^[k]`-image) and carrying the radicand's **odd** period `2πi` (hypothesis `hloops`) — supplies
`h = fp/fq`, an analytic square root near `γ`, refuted by
`no_analytic_sqrt_bottcherIterate_of_oddPeriod`.  So `hDisc` (disconnected) is reduced to exactly the
existence of the depth-`k` closed odd-period loop (the figure-eight / two-lobe split). -/
theorem bottcherIterateGerm_not_isSquare {c : ℂ} (k : ℕ) {Ext : Set ℂ}
    (hExto : IsOpen Ext) (hExtc : IsConnected Ext)
    (hExtesc : ∀ z ∈ Ext, (quadratic c)^[k] z ∈ escapeOpen c)
    (hloops : ∀ T : Set ℂ, T.Countable →
      ∃ (γ γ' : ℝ → ℂ) (m : ℤ),
        (∀ θ, γ θ ∈ Ext) ∧ Continuous γ ∧ Continuous γ' ∧
        (∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt γ (γ' θ) θ) ∧
        γ (2 * Real.pi) = γ 0 ∧
        (∀ θ : ℝ, (quadratic c)^[k] (γ θ) ∉ T) ∧
        (∫ θ in (0:ℝ)..(2 * Real.pi),
            logDeriv (fun z => bottcherCoord c ((quadratic c)^[k] z)) (γ θ) * γ' θ)
          = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))
    (a : analyticSubring Ext)
    (hae : (Filter.Germ.coeRingHom (𝓟 Ext) (fun z => bottcherCoord c ((quadratic c)^[k] z)))
            = (a : Filter.Germ (𝓟 Ext) ℂ)) :
    haveI := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
    ∀ b : meroField Ext,
      b ^ 2 ≠ algebraMap (analyticSubring Ext) (meroField Ext) a := by
  haveI hdom := isDomain_analyticSubring Ext hExto hExtc.isPreconnected hExtc.nonempty
  intro b hbsq
  set bcit : ℂ → ℂ := fun z => bottcherCoord c ((quadratic c)^[k] z) with hbcit
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
    have hz0 : (Filter.Germ.coeRingHom (𝓟 Ext) bcit) = (0 : Filter.Germ (𝓟 Ext) ℂ) := by
      rw [hae, h, ZeroMemClass.coe_zero]
    rw [germ_eq_zero_iff_eqOn_it] at hz0
    exact bottcherCoord_ne_zero c _ (hz0 hExtc.nonempty.choose_spec)
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
  have hEqOn : ∀ z ∈ Ext, fp z ^ 2 = bcit z * fq z ^ 2 := by
    have hcoeeq : ((fp ^ 2 : ℂ → ℂ) : Filter.Germ (𝓟 Ext) ℂ)
        = ((bcit * fq ^ 2 : ℂ → ℂ) : Filter.Germ (𝓟 Ext) ℂ) := hval
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
    exact hgerm_pq (germ_eq_zero_iff_eqOn_it.mpr (fun z hz => by simp [hcon z hz]))
  have hZcount : {z ∈ Ext | fp z * fq z = 0}.Countable :=
    analyticOnNhd_zeros_countable (hfp.mul hfq) hExtc.isPreconnected hw₀U hw₀ne
  set T : Set ℂ := (fun z => (quadratic c)^[k] z) '' {z ∈ Ext | fp z * fq z = 0} with hTdef
  have hTcount : T.Countable := hZcount.image _
  obtain ⟨γ, γ', m, hγExt, hγcont, hγ'cont, hdγ, hγclosed, havoid, hperiod⟩ :=
    hloops T hTcount
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
    · intro h0; exact havoid θ ⟨γ θ, ⟨hγExt θ, by rw [h0]; ring⟩, rfl⟩
    · intro h0; exact havoid θ ⟨γ θ, ⟨hγExt θ, by rw [h0]; ring⟩, rfl⟩
  have hAesc : ∀ z ∈ A, (quadratic c)^[k] z ∈ escapeOpen c := fun z hz => hExtesc z hz.1
  have hhdiv : AnalyticOnNhd ℂ (fun z => fp z / fq z) A :=
    (hfp.mono (fun z hz => hz.1)).div (hfq.mono (fun z hz => hz.1)) (fun z hz => hz.2.2)
  have hsqA : Set.EqOn (fun z => (fp z / fq z) ^ 2) bcit A := by
    intro z hz
    have hfqz : fq z ≠ 0 := hz.2.2
    have heq := hEqOn z hz.1
    show (fp z / fq z) ^ 2 = bcit z
    rw [div_pow, heq, mul_div_assoc, div_self (pow_ne_zero 2 hfqz), mul_one]
  exact no_analytic_sqrt_bottcherIterate_of_oddPeriod k hAo hAesc hγA hγcont hγ'cont hdγ hγclosed
    hperiod _ hhdiv hsqA

end Bottcher

namespace Bottcher

/-- **[Radical relation] `φ_{c₁}^{2^k} = i a` at the germ level.**  For `U ⊆ Ext` with `U` in the deep
escape regime (`‖c‖ ≤ ‖z‖`, `2 < ‖z‖`), the Böttcher germ `a₁ = bottcherCoord c` on `U` and the radicand
`a = bottcherCoord∘f^[k]` on `Ext` satisfy `(algebraMap a₁)^{2^k} = restrictMeroHom (algebraMap a)` —
exactly the radical-relation clause of `Q62RadicalReduction.q62_disconnected_of_radical_data`'s `data`
(with `i = restrictMeroHom`), discharged from `bottcherCoord_iterate`.  Together with
`bottcherIterateGerm_not_isSquare` (the non-square clause) this assembles two of the three analytic
clauses of the `data` tuple; the third (`i GB = φ_{c₂}`, with `GB` the `φ_{c₂}` germ on `Ext`) is the
domain-compatibility datum (`φ_{c₂}` single-valued on the deep `Ext` — the `c₁ ≠ c₂` distinct-precritical
input). -/
theorem radical_relation_germ {c : ℂ} {U Ext : Set ℂ} (k : ℕ) (hUExt : U ⊆ Ext)
    (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty)
    (hExto : IsOpen Ext) (hExtc : IsPreconnected Ext) (hExtne : Ext.Nonempty)
    (hUesc : ∀ z ∈ U, ‖c‖ ≤ ‖z‖ ∧ 2 < ‖z‖)
    (a₁ : analyticSubring U) (a : analyticSubring Ext)
    (ha₁ : (a₁ : Filter.Germ (𝓟 U) ℂ) = (↑(bottcherCoord c) : Filter.Germ (𝓟 U) ℂ))
    (ha : (a : Filter.Germ (𝓟 Ext) ℂ)
        = (↑(fun z => bottcherCoord c ((quadratic c)^[k] z)) : Filter.Germ (𝓟 Ext) ℂ)) :
    haveI := isDomain_analyticSubring U hUo hUc hUne
    haveI := isDomain_analyticSubring Ext hExto hExtc hExtne
    (algebraMap (analyticSubring U) (meroField U) a₁) ^ (2 ^ k)
      = restrictMeroHom hUExt hExto hExtc hExtne hUo hUc hUne
          (algebraMap (analyticSubring Ext) (meroField Ext) a) := by
  haveI := isDomain_analyticSubring U hUo hUc hUne
  haveI := isDomain_analyticSubring Ext hExto hExtc hExtne
  rw [restrictMeroHom_algebraMap, ← map_pow]
  congr 1
  apply Subtype.ext
  have hlhs : ((a₁ ^ (2 ^ k) : analyticSubring U) : Filter.Germ (𝓟 U) ℂ)
      = (↑(fun z => bottcherCoord c z ^ (2 ^ k)) : Filter.Germ (𝓟 U) ℂ) := by
    rw [SubmonoidClass.coe_pow, ha₁, ← Filter.Germ.coe_pow]; rfl
  have hrhs : ((restrictAnalytic hUExt a : analyticSubring U) : Filter.Germ (𝓟 U) ℂ)
      = (↑(fun z => bottcherCoord c ((quadratic c)^[k] z)) : Filter.Germ (𝓟 U) ℂ) := by
    show (a : Filter.Germ (𝓟 Ext) ℂ).compTendsto id
        (tendsto_principal_principal.mpr (fun x hx => hUExt hx)) = _
    rw [ha, Filter.Germ.coe_compTendsto]; rfl
  rw [hlhs, hrhs]
  refine Filter.Germ.coe_eq.mpr (Filter.eventually_principal.mpr (fun z hz => ?_))
  exact (bottcherCoord_iterate (hUesc z hz).1 (hUesc z hz).2 k).symm

end Bottcher

namespace Bottcher
open Set

/-- **[Winding period] `∮_σ d log bottcherCoord = ∮_σ d log z` for a closed loop in the escape set.**
Since `bottcherCoord c = z·exp(S)` with `S = ∑ bottcherLogTerm` single-valued analytic on `escapeOpen`
(`logDeriv_bottcherCoord_escape`), `d log bottcherCoord = z⁻¹ dz + dS`, and the single-valued `S`-part
integrates to `0` over the closed loop (FTC).  So the period of `bottcherCoord` over `σ` equals that of
`z` — `2πi` times the winding number of `σ` around `K_c ∋ 0`.  The homotopy-invariant winding period
that turns the deep non-square's odd-period condition into the topological statement
*`f^[k]∘γ` winds oddly*. -/
theorem pathInt_logDeriv_bottcher_eq_inv {c : ℂ} {σ σ' : ℝ → ℂ}
    (hσesc : ∀ θ : ℝ, σ θ ∈ escapeOpen c)
    (hσcont : Continuous σ) (hσ'cont : Continuous σ')
    (hdσ : ∀ θ ∈ Set.Icc (0:ℝ) (2 * Real.pi), HasDerivAt σ (σ' θ) θ)
    (hσclosed : σ (2 * Real.pi) = σ 0) :
    (∫ θ in (0:ℝ)..(2 * Real.pi), logDeriv (bottcherCoord c) (σ θ) * σ' θ)
      = ∫ θ in (0:ℝ)..(2 * Real.pi), (σ θ)⁻¹ * σ' θ := by
  set S : ℂ → ℂ := fun w => ∑' k, bottcherLogTerm c w k with hS
  have hSan : AnalyticOnNhd ℂ S (escapeOpen c) :=
    (differentiableOn_bottcherLogSum c).analyticOnNhd (isOpen_escapeOpen c)
  have hsplit : ∀ θ : ℝ, logDeriv (bottcherCoord c) (σ θ) * σ' θ
      = (σ θ)⁻¹ * σ' θ + deriv S (σ θ) * σ' θ := by
    intro θ; rw [logDeriv_bottcherCoord_escape (hσesc θ)]; ring
  have hScont : Continuous (fun θ => deriv S (σ θ) * σ' θ) :=
    ((hSan.deriv.continuousOn).comp_continuous hσcont hσesc).mul hσ'cont
  have hinvcont : Continuous (fun θ => (σ θ)⁻¹ * σ' θ) := by
    have hne : ∀ θ, σ θ ≠ 0 := by
      intro θ h
      obtain ⟨_, hz2⟩ := mem_escapeOpen_regime (hσesc θ)
      rw [h, norm_zero] at hz2; linarith
    exact (hσcont.inv₀ hne).mul hσ'cont
  have hSzero : (∫ θ in (0:ℝ)..(2 * Real.pi), deriv S (σ θ) * σ' θ) = 0 := by
    have hd : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
        HasDerivAt (fun t => S (σ t)) (deriv S (σ θ) * σ' θ) θ := by
      intro θ hθ
      rw [Set.uIcc_of_le (by positivity)] at hθ
      have hSd : HasDerivAt S (deriv S (σ θ)) (σ θ) :=
        ((hSan (σ θ) (hσesc θ)).differentiableAt).hasDerivAt
      exact hSd.comp θ (hdσ θ hθ)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hScont.intervalIntegrable _ _),
        hσclosed, sub_self]
  rw [intervalIntegral.integral_congr (fun θ _ => hsplit θ),
      intervalIntegral.integral_add (hinvcont.intervalIntegrable _ _)
        (hScont.intervalIntegrable _ _), hSzero, add_zero]

/-- **[Radicand period = image winding] `∮_γ d log(bottcherCoord∘f^[k]) = ∮_{f^[k]∘γ} d log z`.**
Composing the chain-rule reduction (`pathInt_logDeriv_iterate_eq_image`) with the winding period
(`pathInt_logDeriv_bottcher_eq_inv`) on the closed image loop `σ = f^[k]∘γ`: the radicand's period along
`γ` is `2πi` times the winding of `f^[k]∘γ` around `K_c`. -/
theorem pathInt_logDeriv_bottcherIterate_eq_imageInv {c : ℂ} (k : ℕ) {γ γ' : ℝ → ℂ}
    (hesc : ∀ θ : ℝ, (quadratic c)^[k] (γ θ) ∈ escapeOpen c)
    (hdγ : ∀ θ : ℝ, HasDerivAt γ (γ' θ) θ)
    (hγcont : Continuous γ) (hγ'cont : Continuous γ')
    (hclosed : (quadratic c)^[k] (γ (2 * Real.pi)) = (quadratic c)^[k] (γ 0)) :
    (∫ θ in (0:ℝ)..(2 * Real.pi),
        logDeriv (fun z => bottcherCoord c ((quadratic c)^[k] z)) (γ θ) * γ' θ)
      = ∫ θ in (0:ℝ)..(2 * Real.pi),
          ((quadratic c)^[k] (γ θ))⁻¹
            * ((∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ)) * γ' θ) := by
  set σ : ℝ → ℂ := fun t => (quadratic c)^[k] (γ t) with hσdef
  set σ' : ℝ → ℂ := fun t => (∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ t)) * γ' t with hσ'def
  have hσderiv : ∀ θ : ℝ, HasDerivAt σ (σ' θ) θ := fun θ =>
    (hasDerivAt_quadratic_iterate c (γ θ) k).comp θ (hdγ θ)
  have hσcont : Continuous σ :=
    (analyticOnNhd_quadratic_iterate c k).continuousOn.comp_continuous hγcont (fun _ => mem_univ _)
  have hσ'cont : Continuous σ' := by
    have hprod : Continuous (fun t => ∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ t)) := by
      apply continuous_finsetProd
      intro j _
      exact continuous_const.mul
        ((analyticOnNhd_quadratic_iterate c j).continuousOn.comp_continuous hγcont
          (fun _ => mem_univ _))
    exact hprod.mul hγ'cont
  have hstep1 := pathInt_logDeriv_iterate_eq_image (c := c) k hesc (γ := γ) (γ' := γ') (σ' := σ')
    (fun θ _ => rfl)
  rw [hstep1, pathInt_logDeriv_bottcher_eq_inv hesc hσcont hσ'cont
    (fun θ _ => hσderiv θ) hclosed]

/-- **[Deep non-square from image winding] — the topological form.**  No analytic square root of
`bottcherCoord∘f^[k]` near a closed `C¹` loop `γ` in `A` whose `f^[k]`-image winds an **odd** number of
times around `K_c` (`∮_{f^[k]∘γ} d log z = 2πi·(2m+1)`).  Combines
`pathInt_logDeriv_bottcherIterate_eq_imageInv` (radicand period = image winding) with
`no_analytic_sqrt_bottcherIterate_of_oddPeriod`.  This is the cleanest statement of the depth-`k`
non-square: it asks only for a closed loop whose `f^[k]`-image has odd winding — the disconnected
two-lobe / figure-eight datum, with the analytic period entirely discharged. -/
theorem no_analytic_sqrt_bottcherIterate_of_imageWinding {c : ℂ} (k : ℕ) {m : ℤ}
    {A : Set ℂ} (hAo : IsOpen A) (hAesc : ∀ z ∈ A, (quadratic c)^[k] z ∈ escapeOpen c)
    {γ γ' : ℝ → ℂ} (hγA : ∀ θ : ℝ, γ θ ∈ A)
    (hγcont : Continuous γ) (hγ'cont : Continuous γ')
    (hdγ : ∀ θ : ℝ, HasDerivAt γ (γ' θ) θ)
    (hγclosed : γ (2 * Real.pi) = γ 0)
    (hwind : (∫ θ in (0:ℝ)..(2 * Real.pi),
        ((quadratic c)^[k] (γ θ))⁻¹
          * ((∏ j ∈ Finset.range k, 2 * (quadratic c)^[j] (γ θ)) * γ' θ))
      = 2 * (Real.pi : ℂ) * Complex.I * (2 * (m : ℂ) + 1))
    (h : ℂ → ℂ) (hh : AnalyticOnNhd ℂ h A) :
    ¬ Set.EqOn (fun z => h z ^ 2)
        (fun z => bottcherCoord c ((quadratic c)^[k] z)) A := by
  have hesc : ∀ θ : ℝ, (quadratic c)^[k] (γ θ) ∈ escapeOpen c := fun θ => hAesc _ (hγA θ)
  have hclosed' : (quadratic c)^[k] (γ (2 * Real.pi)) = (quadratic c)^[k] (γ 0) := by rw [hγclosed]
  have hperiod := pathInt_logDeriv_bottcherIterate_eq_imageInv k hesc hdγ hγcont hγ'cont hclosed'
  exact no_analytic_sqrt_bottcherIterate_of_oddPeriod k hAo hAesc hγA hγcont hγ'cont
    (fun θ _ => hdγ θ) hγclosed (hperiod.trans hwind) h hh

end Bottcher
