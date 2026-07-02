/-
# `phiB b` is transcendental over `ℂ(z)` for every `‖b‖ ≥ 5`

The parameterized descent.  The `b = 4` machinery (`U0PhiFourDescent`) generalizes verbatim:
the compose-with-`p` embedding and the finite-tower descent work for ANY monic nonconstant
`p ∈ ℂ[z]` (`kappaP`, `descend_algebraicP`), and the germ-field pullback (`germPullback`/`pullAn`)
was already generic.  Instantiating `p := pPolyB b m` (the escape polynomial of parameter `b`)
and consuming `Bottcher.bottcher_transcendental_far` at the parameterized far carrier gives
`phiB_transcendental`: the window branch of EVERY parameter `‖b‖ ≥ 5` is transcendental over
`ℂ(z)` in the meromorphic field of the annulus.
-/
import GaloisForLFunctions.U0.U0PhiFourDescent
import GaloisForLFunctions.U0.U0PhiLargeCarrier

open Complex Set Metric Polynomial Filter Topology Bottcher U0NaturalBoundary
open U0PhiFourFarCarrier U0PhiFourDescent U0PhiLargeWindow U0PhiLargeCarrier

namespace U0PhiLargeDescent

/-! ## The escape polynomial at parameter `b` -/

noncomputable def pPolyB (b : ℂ) (m : ℕ) : Polynomial ℂ :=
  (quadraticPolyIterate b m).comp (quadraticPoly b)

theorem pPolyB_eval (b : ℂ) (m : ℕ) (z : ℂ) : (pPolyB b m).eval z = pMapB b m z := by
  rw [pPolyB, eval_comp, quadraticPolyIterate_eval]
  show (quadratic b)^[m] ((quadraticPoly b).eval z) = pMapB b m z
  have h : (quadraticPoly b).eval z = quadratic b z := by
    rw [quadraticPoly]
    simp [quadratic_apply]
  rw [h]
  rfl

theorem quadraticPoly_monic (b : ℂ) : (quadraticPoly b).Monic := by
  rw [quadraticPoly]
  monicity!

theorem quadraticPolyIterate_monic_B (b : ℂ) (m : ℕ) : (quadraticPolyIterate b m).Monic := by
  induction m with
  | zero =>
    show (X : Polynomial ℂ).Monic
    exact monic_X
  | succ m ih =>
    show ((quadraticPoly b).comp (quadraticPolyIterate b m)).Monic
    refine Monic.comp (quadraticPoly_monic b) ih ?_
    rw [quadraticPolyIterate_natDegree]
    exact pow_ne_zero m two_ne_zero

theorem pPolyB_monic (b : ℂ) (m : ℕ) : (pPolyB b m).Monic := by
  refine Monic.comp (quadraticPolyIterate_monic_B b m) (quadraticPoly_monic b) ?_
  rw [quadraticPoly_natDegree]
  norm_num

theorem pPolyB_natDegree (b : ℂ) (m : ℕ) : (pPolyB b m).natDegree = 2 ^ (m + 1) := by
  rw [pPolyB, natDegree_comp, quadraticPolyIterate_natDegree, quadraticPoly_natDegree, pow_succ]

theorem pPolyB_natDegree_ne_zero (b : ℂ) (m : ℕ) : (pPolyB b m).natDegree ≠ 0 := by
  rw [pPolyB_natDegree]
  exact pow_ne_zero _ two_ne_zero

/-! ## The compose-with-`p` embedding for an arbitrary monic nonconstant `p` -/

theorem comp_eq_zero_iff_of_monic {p : Polynomial ℂ} (hp : p.Monic) (h0 : p.natDegree ≠ 0)
    {a : Polynomial ℂ} :
    a.comp p = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    have hlc : (a.comp p).leadingCoeff = a.leadingCoeff * p.leadingCoeff ^ a.natDegree :=
      leadingCoeff_comp h0
    rw [h, leadingCoeff_zero, hp.leadingCoeff, one_pow, mul_one] at hlc
    exact leadingCoeff_ne_zero.mpr hne hlc.symm
  · intro h
    rw [h, zero_comp]

/-- `a ↦ germ of z ↦ a(p(z))` for an arbitrary `p`. -/
noncomputable def compPolyToMeroP (p : Polynomial ℂ) : Polynomial ℂ →+* meroField annW :=
  (polyToMero annW).comp (eval₂RingHom (C : ℂ →+* Polynomial ℂ) p)

theorem compPolyToMeroP_apply (p a : Polynomial ℂ) :
    compPolyToMeroP p a = polyToMero annW (a.comp p) := rfl

theorem compPolyToMeroP_injective {p : Polynomial ℂ} (hp : p.Monic) (h0 : p.natDegree ≠ 0) :
    Function.Injective (compPolyToMeroP p) := by
  intro a b hab
  rw [compPolyToMeroP_apply, compPolyToMeroP_apply] at hab
  have h3 := polyToMero_injective annW isOpen_annW isPreconnected_annW annW_nonempty
    annW_infinite hab
  have h4 : (a - b).comp p = 0 := by
    rw [sub_comp, h3, sub_self]
  exact sub_eq_zero.mp ((comp_eq_zero_iff_of_monic hp h0).mp h4)

/-- The compose-with-`p` field embedding `ℂ(z) ↪ meroField annW` for arbitrary monic
nonconstant `p`. -/
noncomputable def kappaP {p : Polynomial ℂ} (hp : p.Monic) (h0 : p.natDegree ≠ 0) :
    RatFunc ℂ →+* meroField annW :=
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  IsFractionRing.lift (compPolyToMeroP_injective hp h0)

theorem kappaP_algebraMap {p : Polynomial ℂ} (hp : p.Monic) (h0 : p.natDegree ≠ 0)
    (a : Polynomial ℂ) :
    kappaP hp h0 (algebraMap (Polynomial ℂ) (RatFunc ℂ) a) = polyToMero annW (a.comp p) := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  exact IsFractionRing.lift_algebraMap (compPolyToMeroP_injective hp h0) a

/-- **The descent for an arbitrary monic nonconstant `p`** — the generalization of
`U0PhiFourDescent.descend_algebraic`. -/
theorem descend_algebraicP {p : Polynomial ℂ} (hp : p.Monic) (h0 : p.natDegree ≠ 0)
    (x : meroField annW)
    (Q : Polynomial (RatFunc ℂ)) (hQ0 : Q ≠ 0)
    (hQev : Q.eval₂
      (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite) x = 0) :
    ∃ S : Polynomial (RatFunc ℂ), S ≠ 0 ∧ S.eval₂ (kappaP hp h0) x = 0 := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  letI : Algebra (RatFunc ℂ) (meroField annW) := (kappaP hp h0).toAlgebra
  set ρ := ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite with hρ
  set y : meroField annW := polyToMero annW X with hy
  have hyint : IsIntegral (RatFunc ℂ) y := by
    refine ⟨p.map (algebraMap ℂ (RatFunc ℂ)) - C RatFunc.X, ?_, ?_⟩
    · refine Monic.sub_of_left (hp.map _) ?_
      refine lt_of_le_of_lt degree_C_le ?_
      rw [hp.degree_map, degree_eq_natDegree hp.ne_zero]
      exact_mod_cast Nat.pos_of_ne_zero h0
    · show eval₂ (algebraMap (RatFunc ℂ) (meroField annW)) y _ = 0
      rw [RingHom.algebraMap_toAlgebra, eval₂_sub, eval₂_C, eval₂_map]
      have h1 : (kappaP hp h0).comp (algebraMap ℂ (RatFunc ℂ))
          = (polyToMero annW).comp (C : ℂ →+* Polynomial ℂ) := by
        ext c
        show kappaP hp h0 (algebraMap ℂ (RatFunc ℂ) c) = polyToMero annW (C c)
        rw [IsScalarTower.algebraMap_eq ℂ (Polynomial ℂ) (RatFunc ℂ)]
        show kappaP hp h0 (algebraMap (Polynomial ℂ) (RatFunc ℂ) (algebraMap ℂ (Polynomial ℂ) c))
          = polyToMero annW (C c)
        rw [kappaP_algebraMap]
        show polyToMero annW ((C c).comp p) = polyToMero annW (C c)
        rw [C_comp]
      rw [h1, ← polyToMero_eq_eval₂, ← RatFunc.algebraMap_X, kappaP_algebraMap, X_comp]
      exact sub_self _
  haveI := IntermediateField.adjoin.finiteDimensional hyint
  set E := IntermediateField.adjoin (RatFunc ℂ) {y} with hE
  have hpolyE : ∀ a : Polynomial ℂ, polyToMero annW a ∈ E := by
    intro a
    induction a using Polynomial.induction_on with
    | C c =>
      have hcc : polyToMero annW (C c)
          = algebraMap (RatFunc ℂ) (meroField annW) (algebraMap ℂ (RatFunc ℂ) c) := by
        rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq ℂ (Polynomial ℂ) (RatFunc ℂ)]
        show polyToMero annW (C c)
          = kappaP hp h0 (algebraMap (Polynomial ℂ) (RatFunc ℂ) (algebraMap ℂ (Polynomial ℂ) c))
        rw [kappaP_algebraMap]
        show polyToMero annW (C c) = polyToMero annW ((C c).comp p)
        rw [C_comp]
      rw [hcc]
      exact E.algebraMap_mem _
    | add p' q' hp' hq' =>
      rw [map_add]
      exact E.add_mem hp' hq'
    | monomial n c hc =>
      rw [pow_succ, ← mul_assoc, map_mul]
      refine E.mul_mem hc ?_
      rw [← hy]
      exact IntermediateField.mem_adjoin_simple_self (RatFunc ℂ) y
  have hρE : ∀ r : RatFunc ℂ, ρ r ∈ E := by
    intro r
    rw [hρ, ratfuncToMero_eq_div annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite]
    exact E.div_mem (hpolyE _) (hpolyE _)
  have hcodinj : Function.Injective (ρ.codRestrict E.toSubring hρE) := by
    intro a b hab
    exact ρ.injective (congrArg Subtype.val hab)
  have hxE : IsAlgebraic E x := by
    refine ⟨Q.map (ρ.codRestrict E.toSubring hρE), ?_, ?_⟩
    · intro h
      exact hQ0 ((Polynomial.map_eq_zero_iff hcodinj).mp h)
    · rw [aeval_def, eval₂_map]
      have hcomp : (algebraMap E (meroField annW)).comp (ρ.codRestrict E.toSubring hρE) = ρ := by
        ext r
        rfl
      rw [hcomp]
      exact hQev
  haveI : Algebra.IsIntegral (RatFunc ℂ) E := Algebra.IsIntegral.of_finite _ _
  have hxK : IsAlgebraic (RatFunc ℂ) x := (isIntegral_trans x hxE.isIntegral).isAlgebraic
  obtain ⟨S, hS0, hSev⟩ := hxK
  refine ⟨S, hS0, ?_⟩
  rw [aeval_def, RingHom.algebraMap_toAlgebra] at hSev
  exact hSev

/-! ## The parameterized transcendence theorem -/

/-- The window branch at parameter `b` as an analytic germ on the annulus. -/
noncomputable def phiBAn (b : ℂ) (hb : 5 ≤ ‖b‖) : analyticSubring annW :=
  ⟨Germ.coeRingHom (𝓟 annW) (phiB b), ⟨phiB b, (phiB_analytic hb).mono annW_subset_ball, rfl⟩⟩

/-- **`phiB b` is transcendental over `ℂ(z)` for EVERY `‖b‖ ≥ 5` (UNCONDITIONAL).** -/
theorem phiB_transcendental {b : ℂ} (hb : 5 ≤ ‖b‖) :
    letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
    letI : Algebra (RatFunc ℂ) (meroField annW) :=
      (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
    Transcendental (RatFunc ℂ)
      (algebraMap (analyticSubring annW) (meroField annW) (phiBAn b hb)) := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  letI algR : Algebra (RatFunc ℂ) (meroField annW) :=
    (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
  intro halg
  have hc : (0 : ℂ) ∉ filledJulia b := zero_not_mem_filledJulia_large (by linarith)
  obtain ⟨m, hfar⟩ := exists_far_carrier_B hb
  have hWo : IsOpen (pMapB b m '' annW) := isOpen_pMapB_image hb m
  have hWc : IsPreconnected (pMapB b m '' annW) := isPreconnected_pMapB_image b m
  have hWne : (pMapB b m '' annW).Nonempty := pMapB_image_nonempty b m
  have hWinf : (pMapB b m '' annW).Infinite := pMapB_image_infinite hb m
  letI := isDomain_analyticSubring (pMapB b m '' annW) hWo hWc hWne
  letI algW : Algebra (RatFunc ℂ) (meroField (pMapB b m '' annW)) :=
    (ratfuncToMero (pMapB b m '' annW) hWo hWc hWne hWinf).toAlgebra
  obtain ⟨a₂, ha₂, _⟩ := bottcherFarBound_spec b hc
    (pMapB b m '' annW) hWo hWc hWne hWinf hfar
  have htr := bottcher_transcendental_far b hc hWo hWc hWne hWinf hfar ha₂
  set x : meroField annW :=
    (algebraMap (analyticSubring annW) (meroField annW) (phiBAn b hb)) ^ (2 ^ (m + 1)) with hx
  have hψ : IsAlgebraic (RatFunc ℂ) x :=
    ((isAlgebraic_iff_isIntegral.mp halg).pow _).isAlgebraic
  obtain ⟨Q, hQ0, hQev⟩ := hψ
  rw [aeval_def, RingHom.algebraMap_toAlgebra] at hQev
  obtain ⟨S, hS0, hSev⟩ := descend_algebraicP (pPolyB_monic b m) (pPolyB_natDegree_ne_zero b m)
    x Q hQ0 hQev
  have hmaps : Set.MapsTo (pMapB b m) annW (pMapB b m '' annW) := Set.mapsTo_image _ _
  have hganal : AnalyticOnNhd ℂ (pMapB b m) annW := (pMapB_analyticOnNhd b m).mono (subset_univ _)
  have hsurj : (pMapB b m '' annW) ⊆ pMapB b m '' annW := subset_rfl
  have hpullinj : Function.Injective
      ((algebraMap (analyticSubring annW) (meroField annW)).comp (pullAn hmaps hganal)) :=
    (IsFractionRing.injective (analyticSubring annW) (meroField annW)).comp
      (pullAn_injective hmaps hganal hsurj)
  set Φ : meroField (pMapB b m '' annW) →+* meroField annW := IsFractionRing.lift hpullinj with hΦ
  have hpull_poly : ∀ a : Polynomial ℂ,
      pullAn hmaps hganal (polyToAnalytic (pMapB b m '' annW) a)
        = polyToAnalytic annW (a.comp (pPolyB b m)) := by
    intro a
    apply Subtype.ext
    rw [pullAn_coe]
    have h1 : ((polyToAnalytic (pMapB b m '' annW) a : analyticSubring (pMapB b m '' annW))
        : Germ (𝓟 (pMapB b m '' annW)) ℂ) = ↑(fun z => a.eval z) := rfl
    have h2 : ((polyToAnalytic annW (a.comp (pPolyB b m)) : analyticSubring annW)
        : Germ (𝓟 annW) ℂ) = ↑(fun z => (a.comp (pPolyB b m)).eval z) := rfl
    rw [h1, h2, germPullback_coe, Germ.coe_eq]
    apply eventually_principal.mpr
    intro z _
    show a.eval (pMapB b m z) = (a.comp (pPolyB b m)).eval z
    rw [eval_comp, pPolyB_eval]
  have hΦρ : kappaP (pPolyB_monic b m) (pPolyB_natDegree_ne_zero b m)
      = Φ.comp (ratfuncToMero (pMapB b m '' annW) hWo hWc hWne hWinf) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
    apply RingHom.ext
    intro a
    show kappaP (pPolyB_monic b m) (pPolyB_natDegree_ne_zero b m)
        (algebraMap (Polynomial ℂ) (RatFunc ℂ) a)
      = Φ (ratfuncToMero (pMapB b m '' annW) hWo hWc hWne hWinf
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) a))
    rw [kappaP_algebraMap, ratfuncToMero_algebraMap_polynomial]
    show polyToMero annW (a.comp (pPolyB b m))
      = Φ (algebraMap (analyticSubring (pMapB b m '' annW)) (meroField (pMapB b m '' annW))
          (polyToAnalytic (pMapB b m '' annW) a))
    rw [hΦ, IsFractionRing.lift_algebraMap]
    show polyToMero annW (a.comp (pPolyB b m))
      = algebraMap (analyticSubring annW) (meroField annW)
          (pullAn hmaps hganal (polyToAnalytic (pMapB b m '' annW) a))
    rw [hpull_poly]
    rfl
  have hx2 : Φ (algebraMap (analyticSubring (pMapB b m '' annW))
      (meroField (pMapB b m '' annW)) a₂) = x := by
    rw [hΦ, IsFractionRing.lift_algebraMap]
    show algebraMap (analyticSubring annW) (meroField annW) (pullAn hmaps hganal a₂) = x
    rw [hx, ← map_pow]
    congr 1
    apply Subtype.ext
    rw [pullAn_coe]
    have ha₂v : (a₂ : Germ (𝓟 (pMapB b m '' annW)) ℂ) = ↑(bottcherCoord b) := ha₂.symm
    rw [ha₂v, germPullback_coe]
    have h2 : ((phiBAn b hb ^ (2 ^ (m + 1)) : analyticSubring annW) : Germ (𝓟 annW) ℂ)
        = ↑(phiB b ^ (2 ^ (m + 1))) := by
      rw [SubmonoidClass.coe_pow]
      show ((↑(phiB b) : Germ (𝓟 annW) ℂ)) ^ (2 ^ (m + 1)) = ↑(phiB b ^ (2 ^ (m + 1)))
      exact (Germ.coe_pow (phiB b) (2 ^ (m + 1))).symm
    rw [h2, Germ.coe_eq]
    apply eventually_principal.mpr
    intro z hz
    show bottcherCoord b (pMapB b m z) = (phiB b ^ (2 ^ (m + 1))) z
    have := phiB_pow_pMapB hb m hz
    rw [← this]
    rfl
  have h0 : S.eval₂ (ratfuncToMero (pMapB b m '' annW) hWo hWc hWne hWinf)
      (algebraMap (analyticSubring (pMapB b m '' annW))
        (meroField (pMapB b m '' annW)) a₂) = 0 := by
    apply Φ.injective
    rw [map_zero, hom_eval₂, ← hΦρ, hx2]
    exact hSev
  exact htr ⟨S, hS0, by rw [aeval_def, RingHom.algebraMap_toAlgebra]; exact h0⟩

end U0PhiLargeDescent
