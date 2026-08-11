import GaloisForLFunctions.HTGeometry.EllipticMeroFieldDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.EllipticCompositumRationalBase
import GaloisForLFunctions.HTGeometry.ConstitutiveDoctrineMemorySpectrum

/-!
# From a differentially algebraic germ to a global relation for its normal form

The jet bridge of the meromorphic field runs one way in the tree: a global algebraic differential
equation for the canonical normal form of a fraction of entire functions makes the fraction
differentially algebraic as a germ.  This file runs it the other way.

A relation in the field restricts to a disc on which the denominator does not vanish, where the
fraction is analytic and the analytic jet bridge produces a pointwise relation.  The evaluated
relation is analytic on the whole analytic locus of the normal form — the complement of a countable
set, hence connected — so the identity theorem spreads it there.  At a pole the normal form takes
the value `0`, so multiplying the relation by the value slot absorbs the junk jets and makes the
equation global.

* `analyticAt_mvPolynomialJetEval` — a polynomial in the jets of an analytic function is analytic;
* `differentiallyAlgebraic_toMeromorphicNFOn_of_differentialAlgebraicOver`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

/-- A polynomial in the point and the jets of a function analytic at a point is analytic there. -/
theorem analyticAt_mvPolynomialJetEval {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) {n : ℕ}
    (P : MvPolynomial (Fin (n + 2)) ℂ) :
    AnalyticAt ℂ
      (fun w ↦ MvPolynomial.eval
        (Fin.cons w fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) P) z := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ ↦ c) z)
  | add p q hp hq =>
      have heq : (fun w ↦ MvPolynomial.eval
            (Fin.cons w fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) (p + q))
          = (fun w ↦ MvPolynomial.eval
              (Fin.cons w fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) p)
            + fun w ↦ MvPolynomial.eval
              (Fin.cons w fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) q := by
        funext w
        simp
      rw [heq]
      exact hp.add hq
  | mul_X p i hp =>
      have hgi : AnalyticAt ℂ
          (fun w : ℂ ↦ (Fin.cons w (fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) :
            Fin (n + 2) → ℂ) i) z := by
        refine Fin.cases ?_ ?_ i
        · simp only [Fin.cons_zero]
          exact analyticAt_id
        · intro j
          simpa using analyticAt_iteratedDeriv hf (j : ℕ)
      have heq : (fun w ↦ MvPolynomial.eval
            (Fin.cons w fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) (p * MvPolynomial.X i))
          = (fun w ↦ MvPolynomial.eval
              (Fin.cons w fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) p)
            * fun w : ℂ ↦ (Fin.cons w (fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) f w) :
              Fin (n + 2) → ℂ) i := by
        funext w
        simp
      rw [heq]
      exact hp.mul hgi

set_option maxHeartbeats 1000000 in
/-- **The germ-to-function jet bridge.**  If a fraction of entire representatives is differentially
algebraic as a germ of the global meromorphic field, its canonical meromorphic normal form satisfies
a global algebraic differential equation. -/
theorem differentiallyAlgebraic_toMeromorphicNFOn_of_differentialAlgebraicOver
    {a b : analyticSubring (Set.univ : Set ℂ)} (hb0 : b ≠ 0)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ))
    (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ))
    (hAa : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) A = (a : Germ (𝓟 Set.univ) ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ))
    (hDA : DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b)) :
    DifferentiallyAlgebraic (toMeromorphicNFOn (fun z ↦ A z / B z) (Set.univ : Set ℂ)) := by
  classical
  set H : ℂ → ℂ := fun z ↦ A z / B z with hHdef
  have hHmer : MeromorphicOn H (Set.univ : Set ℂ) := hA.meromorphicOn.div hB.meromorphicOn
  set F : ℂ → ℂ := toMeromorphicNFOn H (Set.univ : Set ℂ) with hFdef
  have hNF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  obtain ⟨z₀, r, hr, hBne⟩ := exists_ball_ne_zero_of_ne_zero hb0 hB hBb
  set V : Set ℂ := Metric.ball z₀ r with hVdef
  have hVo : IsOpen V := Metric.isOpen_ball
  have hVc : IsPreconnected V := (convex_ball z₀ r).isPreconnected
  have hVne : V.Nonempty := ⟨z₀, Metric.mem_ball_self hr⟩
  have hVinf : V.Infinite := infinite_ball z₀ hr
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra (RatFunc ℂ) (meroField V) := (ratfuncToMero V hVo hVc hVne hVinf).toAlgebra
  letI := meroFieldDifferential hVo hVc hVne
  have hAV : AnalyticOnNhd ℂ A V := hA.mono (Set.subset_univ V)
  have hBV : AnalyticOnNhd ℂ B V := hB.mono (Set.subset_univ V)
  have hHV : AnalyticOnNhd ℂ H V := hAV.div hBV fun z hz ↦ hBne z hz
  -- the restriction of the germ is the analytic realization on the disc
  have hHB : analyticMeroElement H hHV * analyticMeroElement B hBV
      = analyticMeroElement A hAV := by
    rw [← analyticMeroElement_mul hHV hBV]
    have hfun : analyticFunctionElement (fun z ↦ H z * B z) (hHV.mul hBV)
        = analyticFunctionElement A hAV := by
      apply Subtype.ext
      change ((fun z ↦ H z * B z : ℂ → ℂ) : Germ (𝓟 V) ℂ) = ((A : ℂ → ℂ) : Germ (𝓟 V) ℂ)
      rw [Germ.coe_eq]
      refine eventually_principal.mpr fun z hz ↦ ?_
      have hBz : B z ≠ 0 := hBne z hz
      simp only [hHdef]
      field_simp
    unfold analyticMeroElement
    rw [hfun]
  set ρ := restrictMeroAlgHomRatFunc (Set.subset_univ V) isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ hVo hVc hVne hVinf with hρdef
  have hρa : ρ (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a)
      = analyticMeroElement A hAV := by
    rw [hρdef]
    change Bottcher.restrictMeroHom (Set.subset_univ V) isOpen_univ isPreconnected_univ
      Set.univ_nonempty hVo hVc hVne _ = _
    rw [Bottcher.restrictMeroHom_algebraMap, restrictAnalytic_analyticFunctionElement _ hA hAa]
    rfl
  have hρb : ρ (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b)
      = analyticMeroElement B hBV := by
    rw [hρdef]
    change Bottcher.restrictMeroHom (Set.subset_univ V) isOpen_univ isPreconnected_univ
      Set.univ_nonempty hVo hVc hVne _ = _
    rw [Bottcher.restrictMeroHom_algebraMap, restrictAnalytic_analyticFunctionElement _ hB hBb]
    rfl
  have hBVne : analyticMeroElement B hBV ≠ 0 := by
    intro hzero
    have hgerm : analyticFunctionElement B hBV = 0 := by
      apply IsFractionRing.injective (analyticSubring V) (meroField V)
      rw [map_zero]
      exact hzero
    have hval := congrArg Subtype.val hgerm
    rw [ZeroMemClass.coe_zero] at hval
    change ((B : ℂ → ℂ) : Germ (𝓟 V) ℂ) = 0 at hval
    rw [← Germ.coe_zero, Germ.coe_eq] at hval
    exact hBne z₀ (Metric.mem_ball_self hr)
      (eventually_principal.mp hval z₀ (Metric.mem_ball_self hr))
  have hρx : ρ (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
      algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b)
      = analyticMeroElement H hHV := by
    rw [map_div₀, hρa, hρb, ← hHB, mul_div_assoc, div_self hBVne, mul_one]
  have hρderiv : ∀ y : meroField (Set.univ : Set ℂ), ρ y′ = (ρ y)′ := fun y ↦
    restrictMeroAlgHomRatFunc_deriv (Set.subset_univ V) isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ hVo hVc hVne hVinf y
  have hDAV : DifferentialAlgebraicOver (RatFunc ℂ) (analyticMeroElement H hHV) := by
    rw [← hρx]
    by_contra hcon
    exact ((hypertranscendentalOver_algHom_iff ρ hρderiv _).mp hcon) hDA
  obtain ⟨n, P, hP0, hrelV⟩ :=
    exists_relation_of_differentialAlgebraicOver_analyticMeroElement hVo hVc hVne hVinf hHV hDAV
  -- the analytic locus of the normal form is open, connected, and contains the disc
  set N : Set ℂ := {z : ℂ | AnalyticAt ℂ F z}ᶜ with hNdef
  have hNcount : N.Countable :=
    Meromorphic.countable_compl_analyticAt fun z ↦ hNF.meromorphicOn z (Set.mem_univ z)
  set W : Set ℂ := {z : ℂ | AnalyticAt ℂ F z} with hWdef
  have hWo : IsOpen W := isOpen_analyticAt ℂ F
  have hWconn : IsPreconnected W := by
    have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
      rw [Complex.rank_real_complex]
      norm_num
    have hpath := Set.Countable.isPathConnected_compl_of_one_lt_rank hrank hNcount
    have hWN : W = Nᶜ := by
      rw [hNdef, hWdef, compl_compl]
    rw [hWN]
    exact hpath.isConnected.isPreconnected
  have hFH : ∀ z ∈ V, F =ᶠ[𝓝 z] H ∧ AnalyticAt ℂ F z := by
    intro z hz
    have hHan : AnalyticAt ℂ H z := hHV z hz
    have hHord : 0 ≤ meromorphicOrderAt H z :=
      hHan.meromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt.mpr hHan
    have hFord : 0 ≤ meromorphicOrderAt F z := by
      rw [hFdef, meromorphicOrderAt_toMeromorphicNFOn hHmer (Set.mem_univ z)]
      exact hHord
    have hFan : AnalyticAt ℂ F z :=
      (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hFord
    have hpunct : F =ᶠ[𝓝[≠] z] H := by
      rw [hFdef]
      exact hHmer.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
    exact ⟨eventuallyEq_nhds_of_nhdsNE_of_continuousAt hpunct hFan.continuousAt hHan.continuousAt,
      hFan⟩
  have hVW : V ⊆ W := fun z hz ↦ (hFH z hz).2
  -- the evaluated relation is analytic on the locus and vanishes on the disc
  set R : ℂ → ℂ := fun z ↦ MvPolynomial.eval
    (Fin.cons z fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) F z) P with hRdef
  have hRan : AnalyticOnNhd ℂ R W := fun z hz ↦ analyticAt_mvPolynomialJetEval hz P
  have hRV : ∀ z ∈ V, R z = 0 := by
    intro z hz
    have hjets : (fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) F z)
        = fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) H z := by
      funext j
      exact Filter.EventuallyEq.iteratedDeriv_eq (j : ℕ) (hFH z hz).1
    rw [hRdef]
    simp only
    rw [hjets]
    exact hrelV z hz
  have hRW : Set.EqOn R 0 W := by
    refine hRan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hWconn (hVW hVne.choose_spec) ?_
    filter_upwards [hVo.mem_nhds hVne.choose_spec] with w hw
    exact hRV w hw
  -- multiply by the value slot to absorb the junk jets at the poles
  refine ⟨n, P * MvPolynomial.X 1, mul_ne_zero hP0 (MvPolynomial.X_ne_zero 1), fun z ↦ ?_⟩
  have hsplit : MvPolynomial.eval
      (Fin.cons z fun j : Fin (n + 1) ↦ iteratedDeriv (j : ℕ) F z) (P * MvPolynomial.X 1)
      = R z * F z := by
    rw [map_mul, MvPolynomial.eval_X, hRdef]
    congr 1
  rw [hsplit]
  by_cases hz : z ∈ W
  · rw [hRW hz]
    simp
  · have hord : meromorphicOrderAt F z < 0 := by
      by_contra hcon
      exact hz ((hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (not_lt.mp hcon))
    rw [eq_zero_of_meromorphicOrderAt_neg (hNF (Set.mem_univ z)) hord, mul_zero]

end

end GaloisForLFunctions.HTGeometry
