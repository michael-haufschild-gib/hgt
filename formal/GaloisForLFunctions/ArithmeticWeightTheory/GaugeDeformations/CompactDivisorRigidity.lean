import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.QuadraticGaugeRigidity
import GaloisForLFunctions.HTGeometry.DivisorPairing
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteRouche

/-!
# Compact divisor rigidity of gauge continuations

A net of holomorphic regularized gauge fibres converging locally uniformly
to the entire zeta residue factor eventually has exactly its zero divisor
on each compact subset of the continuation half-plane.

Real nonvanishing follows from compact convergence below the pole and the
Euler product above it. Paired multiplicity conservation and convergence
of leading derivatives force each individual multiplicity to stabilize.
Finiteness of the zeta zero set on a compact set makes this simultaneous.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticCorrelationGeometry GaloisForLFunctions.PrimeTorusTheory
open RHTower
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations

/-- The entire residue factor respects Schwarz reflection. -/
theorem zetaResidueFactor_conj (s : ℂ) :
    zetaResidueFactor (conj s) = conj (zetaResidueFactor s) := by
  by_cases hs : s = 1
  · subst s
    simp only [map_one, zetaResidueFactor_one]
  have hc : conj s ≠ 1 := by
    intro h
    have hh := congrArg conj h
    simp only [Complex.conj_conj, map_one] at hh
    exact hs hh
  rw [zetaResidueFactor_of_ne hc, zetaResidueFactor_of_ne hs,
    map_mul, map_sub, map_one, riemannZeta_conj]

/-- The residue factor is nowhere locally zero, hence has finite order everywhere. -/
theorem zetaResidueFactor_order_ne_top (s : ℂ) :
    analyticOrderAt zetaResidueFactor s ≠ ⊤ := by
  intro htop
  have hZ : AnalyticOnNhd ℂ zetaResidueFactor univ :=
    fun z _ => differentiable_zetaResidueFactor.analyticAt z
  have heq := hZ.eq_of_eventuallyEq analyticOnNhd_const (analyticOrderAt_eq_top.mp htop)
  have h := congrFun heq 1
  exact one_ne_zero (by simpa only [zetaResidueFactor_one] using h)

theorem zetaResidueFactor_order_conj (s : ℂ) :
    analyticOrderAt zetaResidueFactor (conj s) = analyticOrderAt zetaResidueFactor s :=
  analyticOrderAt_conj_of_conjEquivariant zetaResidueFactor_conj
    (differentiable_zetaResidueFactor.analyticAt s)
    (differentiable_zetaResidueFactor.analyticAt (conj s))

/-- A nonzero derivative bounds the order at its index. -/
theorem analyticOrderAt_le_nat_of_nonzero_jet {f : ℂ → ℂ} {s : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f s) (hm : iteratedDeriv m f s ≠ 0) :
    analyticOrderAt f s ≤ m := by
  by_contra h
  have hge : ((m + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt f s := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (ENat.coe_add_one_le_iff.mpr (lt_of_not_ge h))
  exact hm ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mp hge m
    (Nat.lt_succ_self m))

/-- Locally uniform holomorphic convergence preserves every derivative. -/
theorem locallyUniform_iteratedDeriv {ι : Type*} {φ : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hF : ∀ i, AnalyticOnNhd ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F f φ Ω) (m : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv m (F i))
      (iteratedDeriv m f) φ Ω := by
  induction m with
  | zero => simpa only [iteratedDeriv_zero] using hconv
  | succ m ih =>
    have hd : ∀ i, DifferentiableOn ℂ (iteratedDeriv m (F i)) Ω := fun i =>
      HTGeometry.differentiableOn_iteratedDeriv_of_isOpen (hF i).differentiableOn hΩ m
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      ih.deriv (Eventually.of_forall hd) hΩ

/-- A nonzero limiting leading jet prevents multiplicity from increasing. -/
theorem eventually_order_le_of_locallyUniform {ι : Type*} {φ : Filter ι}
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hF : ∀ i, AnalyticOnNhd ℂ (F i) Ω)
    (hconv : TendstoLocallyUniformlyOn F f φ Ω) {s : ℂ} (hs : s ∈ Ω)
    (hf : AnalyticAt ℂ f s) (hfinite : analyticOrderAt f s ≠ ⊤) :
    ∀ᶠ i in φ, analyticOrderAt (F i) s ≤ analyticOrderAt f s := by
  let m := (analyticOrderAt f s).toNat
  have hm : (m : ℕ∞) = analyticOrderAt f s := ENat.coe_toNat hfinite
  have hjet : iteratedDeriv m f s ≠ 0 :=
    ((analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hf).mp hm.symm).2
  have hlim := (locallyUniform_iteratedDeriv hΩ hF hconv m).tendsto_at hs
  filter_upwards [hlim.eventually_ne hjet] with i hi
  rw [← hm]
  exact analyticOrderAt_le_nat_of_nonzero_jet (hF i s hs) hi

/-- Compact convergence controls the real interval up to the pole; the
Euler product supplies nonvanishing on the rest of the real ray. -/
theorem eventually_real_nonvanishing {ι : Type*} {φ : Filter ι}
    {c d : ℝ} (hc : 1 / 2 ≤ c) (hcd : c < d)
    {x : ι → GaugeTorus} {U : ι → ℂ → ℂ}
    (hUeq : ∀ i s, 1 < s.re → U i s = (s - 1) * gaugeFibre (x i) s)
    (hconv : TendstoLocallyUniformlyOn U zetaResidueFactor φ {s : ℂ | c < s.re}) :
    ∀ᶠ i in φ, ∀ t : ℝ, d < t → U i (t : ℂ) ≠ 0 := by
  let K : Set ℂ := Complex.ofReal '' Icc d 1
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hsub : K ⊆ {s : ℂ | c < s.re} := by
    rintro _ ⟨t, ht, rfl⟩
    exact hcd.trans_le ht.1
  have hne : ∀ s ∈ K, zetaResidueFactor s ≠ 0 := by
    rintro _ ⟨t, ht, rfl⟩
    exact zetaResidueFactor_real_ne_zero (by linarith only [hc, hcd, ht.1])
  have he := RiemannGaussian.eventually_forall_norm_sub_lt_norm_on_compact_of_tendstoLocallyUniformlyOn
    hconv (isOpen_lt continuous_const Complex.continuous_re) hK hsub
    differentiable_zetaResidueFactor.continuous.continuousOn hne
  filter_upwards [he] with i hi t ht
  by_cases ht1 : t ≤ 1
  · have h := hi (t : ℂ) ⟨t, ⟨ht.le, ht1⟩, rfl⟩
    intro hz
    rw [hz, zero_sub, norm_neg] at h
    exact lt_irrefl _ h
  · have ht1' : 1 < (t : ℂ).re := lt_of_not_ge ht1
    rw [hUeq i t ht1', gaugeFibre_eq_zeta_mul_exp (x i) ht1']
    exact mul_ne_zero (sub_ne_zero.mpr (by exact_mod_cast (ne_of_gt (lt_of_not_ge ht1))))
      (mul_ne_zero (riemannZeta_ne_zero_of_one_lt_re ht1') (Complex.exp_ne_zero _))


/-- Leading jets bound both conjugate multiplicities from above. Their
conserved sum then forces each multiplicity to equal its zeta value. -/
theorem eventually_gauge_order_eq {ι : Type*} {φ : Filter ι}
    {c : ℝ} (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1)
    {x : ι → GaugeTorus} {U : ι → ℂ → ℂ}
    (hU : ∀ i, AnalyticOnNhd ℂ (U i) {s : ℂ | c < s.re})
    (hUeq : ∀ i s, 1 < s.re → U i s = (s - 1) * gaugeFibre (x i) s)
    (hconv : TendstoLocallyUniformlyOn U zetaResidueFactor φ {s : ℂ | c < s.re})
    {s : ℂ} (hs : c < s.re) :
    ∀ᶠ i in φ, analyticOrderAt (U i) s = analyticOrderAt zetaResidueFactor s := by
  obtain ⟨d, hcd, hdm⟩ := exists_between (lt_min hc₁ hs)
  have hd₁ : d < 1 := hdm.trans_le (min_le_left _ _)
  have hds : d < s.re := hdm.trans_le (min_le_right _ _)
  have hopen : IsOpen {s : ℂ | c < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hleft := eventually_order_le_of_locallyUniform hopen hU hconv hs
    (differentiable_zetaResidueFactor.analyticAt s) (zetaResidueFactor_order_ne_top s)
  have hcs : c < (conj s).re := by simpa only [Complex.conj_re] using hs
  have hright := eventually_order_le_of_locallyUniform hopen hU hconv hcs
    (differentiable_zetaResidueFactor.analyticAt (conj s)) (zetaResidueFactor_order_ne_top (conj s))
  filter_upwards [eventually_real_nonvanishing hc₀ hcd hUeq hconv, hleft, hright]
    with i hreal hl hr
  rw [zetaResidueFactor_order_conj] at hr
  have hUi : AnalyticOnNhd ℂ (U i) {z : ℂ | d < z.re} :=
    (hU i).mono (fun z hz => hcd.trans hz)
  have hpair := (gauge_quadratic_rigidity (hc₀.trans hcd.le) hd₁ hUi (hUeq i) hreal).2.2.2 s hds
  rw [analyticOrderAt_schwarzConjugate hUi hds] at hpair
  have hlf : analyticOrderAt (U i) s ≠ ⊤ :=
    ne_top_of_le_ne_top (zetaResidueFactor_order_ne_top s) hl
  have hrf : analyticOrderAt (U i) (conj s) ≠ ⊤ :=
    ne_top_of_le_ne_top (zetaResidueFactor_order_ne_top s) hr
  let a := (analyticOrderAt (U i) s).toNat
  let b := (analyticOrderAt (U i) (conj s)).toNat
  let m := (analyticOrderAt zetaResidueFactor s).toNat
  have ha : (a : ℕ∞) = analyticOrderAt (U i) s := ENat.coe_toNat hlf
  have hb : (b : ℕ∞) = analyticOrderAt (U i) (conj s) := ENat.coe_toNat hrf
  have hm : (m : ℕ∞) = analyticOrderAt zetaResidueFactor s :=
    ENat.coe_toNat (zetaResidueFactor_order_ne_top s)
  rw [← ha, ← hm] at hl
  rw [← hb, ← hm] at hr
  rw [← ha, ← hb, ← hm] at hpair
  have hal : a ≤ m := by exact_mod_cast hl
  have hbl : b ≤ m := by exact_mod_cast hr
  have hab : a + b = m + m := by exact_mod_cast hpair
  have ham : a = m := by omega
  rw [← ha, ← hm, ham]

/-- A compact subset of an open half-plane admits a strictly smaller
half-plane that still contains it and includes the pole. -/
theorem exists_halfPlane_cut_for_compact {c : ℝ} (hc : c < 1) {K : Set ℂ}
    (hK : IsCompact K) (hKc : K ⊆ {s : ℂ | c < s.re}) :
    ∃ d : ℝ, c < d ∧ d < 1 ∧ ∀ s ∈ K, d < s.re := by
  have hgap : ContinuousOn (fun s : ℂ => s.re - c) K :=
    (Complex.continuous_re.sub continuous_const).continuousOn
  obtain ⟨ε, hε, hεK⟩ := hK.exists_forall_le' hgap
    (fun s hs => sub_pos.mpr (hKc hs))
  refine ⟨min ((c + 1) / 2) (c + ε / 2), ?_, ?_, ?_⟩
  · exact lt_min (by linarith only [hc]) (by linarith only [hε])
  · exact (min_le_left _ _).trans_lt (by linarith only [hc])
  · intro s hs
    exact (min_le_right _ _).trans_lt (by have hh := hεK s hs; linarith only [hh, hε])

/-- Compact-open convergence of genuine regularized gauge fibres to zeta
makes their entire zero divisors equal on each compact subset eventually. -/
theorem eventually_gauge_divisor_eq_on_compact {ι : Type*} {φ : Filter ι}
    {c : ℝ} (hc₀ : 1 / 2 ≤ c) (hc₁ : c < 1)
    {x : ι → GaugeTorus} {U : ι → ℂ → ℂ}
    (hU : ∀ i, AnalyticOnNhd ℂ (U i) {s : ℂ | c < s.re})
    (hUeq : ∀ i s, 1 < s.re → U i s = (s - 1) * gaugeFibre (x i) s)
    (hconv : TendstoLocallyUniformlyOn U zetaResidueFactor φ {s : ℂ | c < s.re})
    {K : Set ℂ} (hK : IsCompact K) (hKc : K ⊆ {s : ℂ | c < s.re}) :
    ∀ᶠ i in φ, ∀ s ∈ K, analyticOrderAt (U i) s = analyticOrderAt zetaResidueFactor s := by
  have hfinite : (K ∩ {s | zetaResidueFactor s = 0}).Finite :=
    HTGeometry.finite_zeros_of_isCompact isOpen_univ
      differentiable_zetaResidueFactor.differentiableOn
      (fun s _ he => zetaResidueFactor_order_ne_top s (analyticOrderAt_eq_top.mpr he))
      hK (subset_univ K)
  have hzeros : ∀ᶠ i in φ, ∀ s ∈ K ∩ {s | zetaResidueFactor s = 0},
      analyticOrderAt (U i) s = analyticOrderAt zetaResidueFactor s := by
    exact (Filter.eventually_all_finite hfinite).mpr (fun s hs =>
      eventually_gauge_order_eq hc₀ hc₁ hU hUeq hconv (hKc hs.1))
  obtain ⟨d, hcd, hd₁, hdK⟩ := exists_halfPlane_cut_for_compact hc₁ hK hKc
  filter_upwards [hzeros, eventually_real_nonvanishing hc₀ hcd hUeq hconv]
    with i hi hreal s hs
  by_cases hz : zetaResidueFactor s = 0
  · exact hi s ⟨hs, hz⟩
  have hUi : AnalyticOnNhd ℂ (U i) {z : ℂ | d < z.re} :=
    (hU i).mono (fun z hz => hcd.trans hz)
  have hUnz : U i s ≠ 0 := by
    intro hzero
    exact hz ((gauge_paired_zero_iff (hc₀.trans hcd.le) hd₁ hUi (hUeq i) hreal
      (hdK s hs)).mp (Or.inl hzero))
  rw [analyticOrderAt_eq_zero.mpr (Or.inr hUnz), analyticOrderAt_eq_zero.mpr (Or.inr hz)]

#print axioms eventually_gauge_order_eq
#print axioms eventually_gauge_divisor_eq_on_compact
end GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations
