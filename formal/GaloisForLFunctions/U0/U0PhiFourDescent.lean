/-
# `phiFour` is transcendental over `ℂ(z)` — the dyadic pullback descent

The φ-side of the `b = 4` window capstone.  Suppose the window branch `phiFour` were algebraic
over `ℂ(z)` in the meromorphic field of the annulus `annW = {1 < ‖z‖ < 21/20}`.  Then so is the
dyadic power `phiFour^(2^(m+1)) = bottcherCoord 4 ∘ pMap m` (`phiFour_pow_iterate`).  The descent:

1. **Finite tower** (`descend_algebraic`): inside `meroField annW`, the identity germ `y = [z]` is
   *integral* over the compose-with-`p` embedding `κ : ℂ(z) ↪ meroField annW`,
   `κ(r) = [r ∘ p]` (`p = pPoly m`, monic of degree `2^{m+1}`), via the monic witness
   `p(T) − X`.  Every `ℂ(z)`-germ lies in `κ(ℂ(z))⟮y⟯`, which is finite over `κ(ℂ(z))`; so
   algebraicity over the usual embedding `ρ` descends to algebraicity over `κ`
   (`isIntegral_trans`).  The coefficients of the new relation are rational functions **of `p(z)`**.
2. **Pullback transport**: precomposition with `pMap m` is a field embedding
   `meroField (pMap m '' annW) ↪ meroField annW` matching `κ` with the standard embedding of
   `ℂ(w)` on the far image and matching the genuine Böttcher germ (supplied by
   `bottcherFarBound_spec`) with `phiFour^(2^(m+1))`.  The descended relation therefore transports
   to an algebraic relation for the Böttcher germ on the far carrier — contradicting
   `Bottcher.bottcher_transcendental_far`.

Conclusion: `phiFour_transcendental` — the window branch is transcendental over `ℂ(z)`,
unconditionally.  This is the `u₀`-degree-0 residue of the window engine, closed.
-/
import GaloisForLFunctions.U0.U0PhiFourFarCarrier
import GaloisForLFunctions.Bottcher.BasinBranching

open Complex Set Metric Polynomial Filter Topology Bottcher U0NaturalBoundary U0PhiFourWindow
open U0PhiFourFarCarrier

namespace U0PhiFourDescent

/-! ## The escape map as a monic polynomial -/

/-- `pMap m` as a polynomial: the iterate polynomial composed with one quadratic step. -/
noncomputable def pPoly (m : ℕ) : Polynomial ℂ :=
  (quadraticPolyIterate 4 m).comp (quadraticPoly 4)

theorem pPoly_eval (m : ℕ) (z : ℂ) : (pPoly m).eval z = pMap m z := by
  rw [pPoly, eval_comp, quadraticPolyIterate_eval]
  show (quadratic 4)^[m] ((quadraticPoly 4).eval z) = pMap m z
  have h : (quadraticPoly 4).eval z = quadratic 4 z := by
    rw [quadraticPoly]
    simp [quadratic_apply]
  rw [h]
  rfl

theorem quadraticPolyIterate_monic (m : ℕ) : (quadraticPolyIterate (4 : ℂ) m).Monic := by
  induction m with
  | zero =>
    show (X : Polynomial ℂ).Monic
    exact monic_X
  | succ m ih =>
    show ((quadraticPoly 4).comp (quadraticPolyIterate (4 : ℂ) m)).Monic
    refine Monic.comp ?_ ih ?_
    · rw [quadraticPoly]
      monicity!
    · rw [quadraticPolyIterate_natDegree]
      exact pow_ne_zero m two_ne_zero

theorem pPoly_monic (m : ℕ) : (pPoly m).Monic := by
  refine Monic.comp (quadraticPolyIterate_monic m) ?_ ?_
  · rw [quadraticPoly]
    monicity!
  · rw [quadraticPoly_natDegree]
    norm_num

theorem pPoly_natDegree (m : ℕ) : (pPoly m).natDegree = 2 ^ (m + 1) := by
  rw [pPoly, natDegree_comp, quadraticPolyIterate_natDegree, quadraticPoly_natDegree, pow_succ]

theorem pPoly_natDegree_ne_zero (m : ℕ) : (pPoly m).natDegree ≠ 0 := by
  rw [pPoly_natDegree]
  exact pow_ne_zero _ two_ne_zero

theorem comp_pPoly_eq_zero_iff (m : ℕ) {a : Polynomial ℂ} :
    a.comp (pPoly m) = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra hne
    have hlc : (a.comp (pPoly m)).leadingCoeff
        = a.leadingCoeff * (pPoly m).leadingCoeff ^ a.natDegree :=
      leadingCoeff_comp (pPoly_natDegree_ne_zero m)
    rw [h, leadingCoeff_zero, (pPoly_monic m).leadingCoeff, one_pow, mul_one] at hlc
    exact leadingCoeff_ne_zero.mpr hne hlc.symm
  · intro h
    rw [h, zero_comp]

/-! ## The compose-with-`p` embedding `κ : ℂ(z) ↪ meroField annW` -/

/-- `a ↦ germ of z ↦ a(p(z))`: polynomials into the meromorphic field through the escape map. -/
noncomputable def compPolyToMero (m : ℕ) : Polynomial ℂ →+* meroField annW :=
  (polyToMero annW).comp (eval₂RingHom (C : ℂ →+* Polynomial ℂ) (pPoly m))

theorem compPolyToMero_apply (m : ℕ) (a : Polynomial ℂ) :
    compPolyToMero m a = polyToMero annW (a.comp (pPoly m)) := rfl

theorem compPolyToMero_injective (m : ℕ) : Function.Injective (compPolyToMero m) := by
  intro a b hab
  rw [compPolyToMero_apply, compPolyToMero_apply] at hab
  have h3 := polyToMero_injective annW isOpen_annW isPreconnected_annW annW_nonempty
    annW_infinite hab
  have h4 : (a - b).comp (pPoly m) = 0 := by
    rw [sub_comp, h3, sub_self]
  exact sub_eq_zero.mp ((comp_pPoly_eq_zero_iff m).mp h4)

/-- **The compose-with-`p` field embedding** `κ : ℂ(z) ↪ meroField annW`,
`κ(r) = [z ↦ r(p(z))]`. -/
noncomputable def kappa (m : ℕ) : RatFunc ℂ →+* meroField annW :=
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  IsFractionRing.lift (compPolyToMero_injective m)

theorem kappa_algebraMap (m : ℕ) (a : Polynomial ℂ) :
    kappa m (algebraMap (Polynomial ℂ) (RatFunc ℂ) a) = polyToMero annW (a.comp (pPoly m)) := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  exact IsFractionRing.lift_algebraMap (compPolyToMero_injective m) a

/-! ## `polyToMero` as evaluation at the identity germ -/

theorem polyToMero_eq_eval₂ (a : Polynomial ℂ) :
    polyToMero annW a
      = a.eval₂ ((polyToMero annW).comp (C : ℂ →+* Polynomial ℂ)) (polyToMero annW X) := by
  have h : (polyToMero annW)
      = eval₂RingHom ((polyToMero annW).comp (C : ℂ →+* Polynomial ℂ)) (polyToMero annW X) := by
    apply ringHom_ext
    · intro c
      simp [coe_eval₂RingHom, eval₂_C]
    · simp [coe_eval₂RingHom, eval₂_X]
  conv_lhs => rw [h]
  simp [coe_eval₂RingHom]

/-! ## The descent through the finite tower `κ(ℂ(z)) ⊆ κ(ℂ(z))⟮[z]⟯ ∋ ℂ(z)-germs` -/

/-- **Algebraicity descends from `ℂ(z)` to `ℂ(p(z))`.**  If `x ∈ meroField annW` satisfies a
nonzero polynomial relation with coefficients the germs of rational functions of `z`, it satisfies
one whose coefficients are germs of rational functions of `p(z)` — because `[z]` is integral over
`κ(ℂ(z))` (monic witness `p(T) − X`) and every `ℂ(z)`-germ is a rational expression in `[z]`. -/
theorem descend_algebraic (m : ℕ) (x : meroField annW)
    (Q : Polynomial (RatFunc ℂ)) (hQ0 : Q ≠ 0)
    (hQev : Q.eval₂
      (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite) x = 0) :
    ∃ S : Polynomial (RatFunc ℂ), S ≠ 0 ∧ S.eval₂ (kappa m) x = 0 := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  letI : Algebra (RatFunc ℂ) (meroField annW) := (kappa m).toAlgebra
  set ρ := ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite with hρ
  set y : meroField annW := polyToMero annW X with hy
  -- the identity germ is integral over the compose-with-p base field
  have hyint : IsIntegral (RatFunc ℂ) y := by
    refine ⟨(pPoly m).map (algebraMap ℂ (RatFunc ℂ)) - C RatFunc.X, ?_, ?_⟩
    · refine Monic.sub_of_left ((pPoly_monic m).map _) ?_
      refine lt_of_le_of_lt degree_C_le ?_
      rw [(pPoly_monic m).degree_map, degree_eq_natDegree (pPoly_monic m).ne_zero,
        pPoly_natDegree]
      exact_mod_cast pow_pos (by norm_num : (0 : ℕ) < 2) (m + 1)
    · show eval₂ (algebraMap (RatFunc ℂ) (meroField annW)) y _ = 0
      rw [RingHom.algebraMap_toAlgebra, eval₂_sub, eval₂_C, eval₂_map]
      have h1 : (kappa m).comp (algebraMap ℂ (RatFunc ℂ))
          = (polyToMero annW).comp (C : ℂ →+* Polynomial ℂ) := by
        ext c
        show kappa m (algebraMap ℂ (RatFunc ℂ) c) = polyToMero annW (C c)
        rw [IsScalarTower.algebraMap_eq ℂ (Polynomial ℂ) (RatFunc ℂ)]
        show kappa m (algebraMap (Polynomial ℂ) (RatFunc ℂ) (algebraMap ℂ (Polynomial ℂ) c))
          = polyToMero annW (C c)
        rw [kappa_algebraMap]
        show polyToMero annW ((C c).comp (pPoly m)) = polyToMero annW (C c)
        rw [C_comp]
      rw [h1, ← polyToMero_eq_eval₂, ← RatFunc.algebraMap_X, kappa_algebraMap, X_comp]
      exact sub_self _
  haveI := IntermediateField.adjoin.finiteDimensional hyint
  set E := IntermediateField.adjoin (RatFunc ℂ) {y} with hE
  -- every ℂ(z)-germ lies in the tower field E
  have hpolyE : ∀ a : Polynomial ℂ, polyToMero annW a ∈ E := by
    intro a
    induction a using Polynomial.induction_on with
    | C c =>
      have hcc : polyToMero annW (C c)
          = algebraMap (RatFunc ℂ) (meroField annW) (algebraMap ℂ (RatFunc ℂ) c) := by
        rw [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_eq ℂ (Polynomial ℂ) (RatFunc ℂ)]
        show polyToMero annW (C c)
          = kappa m (algebraMap (Polynomial ℂ) (RatFunc ℂ) (algebraMap ℂ (Polynomial ℂ) c))
        rw [kappa_algebraMap]
        show polyToMero annW (C c) = polyToMero annW ((C c).comp (pPoly m))
        rw [C_comp]
      rw [hcc]
      exact E.algebraMap_mem _
    | add p q hp hq =>
      rw [map_add]
      exact E.add_mem hp hq
    | monomial n c hc =>
      rw [pow_succ, ← mul_assoc, map_mul]
      refine E.mul_mem hc ?_
      rw [← hy]
      exact IntermediateField.mem_adjoin_simple_self (RatFunc ℂ) y
  have hρE : ∀ r : RatFunc ℂ, ρ r ∈ E := by
    intro r
    rw [hρ, ratfuncToMero_eq_div annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite]
    exact E.div_mem (hpolyE _) (hpolyE _)
  -- x is algebraic over E, hence over the compose-with-p base field
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

/-! ## The pullback embedding of germ fields along an analytic surjection -/

section Pullback

variable {S T : Set ℂ} {g : ℂ → ℂ}

/-- Precomposition with `g : S → T` as a ring hom on germs. -/
noncomputable def germPullback (hmaps : Set.MapsTo g S T) :
    Germ (𝓟 T) ℂ →+* Germ (𝓟 S) ℂ where
  toFun := fun a => a.compTendsto g (tendsto_principal_principal.mpr hmaps)
  map_one' := by
    rw [show (1 : Germ (𝓟 T) ℂ) = ((fun _ => (1 : ℂ)) : ℂ → ℂ) from rfl, Germ.coe_compTendsto]
    rfl
  map_mul' := fun a b => by
    induction a using Germ.inductionOn with
    | _ fa =>
      induction b using Germ.inductionOn with
      | _ fb =>
        rw [← Germ.coe_mul, Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto,
          ← Germ.coe_mul]
        rfl
  map_zero' := by
    rw [show (0 : Germ (𝓟 T) ℂ) = ((fun _ => (0 : ℂ)) : ℂ → ℂ) from rfl, Germ.coe_compTendsto]
    rfl
  map_add' := fun a b => by
    induction a using Germ.inductionOn with
    | _ fa =>
      induction b using Germ.inductionOn with
      | _ fb =>
        rw [← Germ.coe_add, Germ.coe_compTendsto, Germ.coe_compTendsto, Germ.coe_compTendsto,
          ← Germ.coe_add]
        rfl

theorem germPullback_coe (hmaps : Set.MapsTo g S T) (f : ℂ → ℂ) :
    germPullback hmaps (↑f : Germ (𝓟 T) ℂ) = ↑(f ∘ g) :=
  Germ.coe_compTendsto f (tendsto_principal_principal.mpr hmaps)

theorem germPullback_mem (hmaps : Set.MapsTo g S T) (hg : AnalyticOnNhd ℂ g S)
    {a : Germ (𝓟 T) ℂ} (ha : a ∈ analyticSubring T) :
    germPullback hmaps a ∈ analyticSubring S := by
  obtain ⟨f, hf, rfl⟩ := ha
  exact ⟨f ∘ g, hf.comp hg hmaps, (germPullback_coe hmaps f).symm⟩

/-- The pullback on analytic subrings. -/
noncomputable def pullAn (hmaps : Set.MapsTo g S T) (hg : AnalyticOnNhd ℂ g S) :
    analyticSubring T →+* analyticSubring S :=
  ((germPullback hmaps).comp (analyticSubring T).subtype).codRestrict (analyticSubring S)
    (fun a => germPullback_mem hmaps hg a.2)

theorem pullAn_coe (hmaps : Set.MapsTo g S T) (hg : AnalyticOnNhd ℂ g S)
    (a : analyticSubring T) :
    ((pullAn hmaps hg a : analyticSubring S) : Germ (𝓟 S) ℂ)
      = germPullback hmaps (a : Germ (𝓟 T) ℂ) := rfl

/-- The pullback is injective when `g` is onto `T`: a function vanishing on `g '' S = T`
vanishes as a `T`-germ. -/
theorem pullAn_injective (hmaps : Set.MapsTo g S T) (hg : AnalyticOnNhd ℂ g S)
    (hsurj : T ⊆ g '' S) :
    Function.Injective (pullAn hmaps hg) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨f, hf, hval⟩ := a.2
  have hval' : (a : Germ (𝓟 T) ℂ) = ↑f := hval.symm
  have hgerm : germPullback hmaps (a : Germ (𝓟 T) ℂ) = 0 := by
    have := congrArg Subtype.val ha
    rwa [pullAn_coe, ZeroMemClass.coe_zero] at this
  rw [hval', germPullback_coe, ← Germ.coe_zero, Germ.coe_eq] at hgerm
  have hS0 : ∀ z ∈ S, f (g z) = 0 := fun z hz => eventually_principal.mp hgerm z hz
  have hT0 : ∀ w ∈ T, f w = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hsurj hw
    exact hS0 z hz
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero, hval', ← Germ.coe_zero, Germ.coe_eq]
  exact eventually_principal.mpr hT0

end Pullback

/-! ## The main theorem -/

/-- The window branch as an analytic germ on the annulus. -/
noncomputable def phiAnnAn : analyticSubring annW :=
  ⟨Germ.coeRingHom (𝓟 annW) phiFour, ⟨phiFour, phiFour_analytic.mono annW_subset_ball, rfl⟩⟩

/-- **`phiFour` is transcendental over `ℂ(z)` (UNCONDITIONAL).**  The window Böttcher branch at
`b = 4` satisfies no nonzero polynomial relation over the rational-function field in the
meromorphic field of the window annulus `{1 < ‖z‖ < 21/20}`.  Descent through the dyadic pullback
chain onto the far carrier, against `Bottcher.bottcher_transcendental_far`. -/
theorem phiFour_transcendental :
    letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
    letI : Algebra (RatFunc ℂ) (meroField annW) :=
      (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
    Transcendental (RatFunc ℂ)
      (algebraMap (analyticSubring annW) (meroField annW) phiAnnAn) := by
  letI := isDomain_analyticSubring annW isOpen_annW isPreconnected_annW annW_nonempty
  letI algR : Algebra (RatFunc ℂ) (meroField annW) :=
    (ratfuncToMero annW isOpen_annW isPreconnected_annW annW_nonempty annW_infinite).toAlgebra
  intro halg
  -- the far carrier
  obtain ⟨m, hfar⟩ := exists_far_carrier
  have hWo : IsOpen (pMap m '' annW) := isOpen_pMap_image m
  have hWc : IsPreconnected (pMap m '' annW) := isPreconnected_pMap_image m
  have hWne : (pMap m '' annW).Nonempty := pMap_image_nonempty m
  have hWinf : (pMap m '' annW).Infinite := pMap_image_infinite m
  letI := isDomain_analyticSubring (pMap m '' annW) hWo hWc hWne
  letI algW : Algebra (RatFunc ℂ) (meroField (pMap m '' annW)) :=
    (ratfuncToMero (pMap m '' annW) hWo hWc hWne hWinf).toAlgebra
  -- the genuine Böttcher germ on the far carrier and its transcendence (parallel-lane theorems)
  obtain ⟨a₂, ha₂, _⟩ := bottcherFarBound_spec 4 zero_not_mem_filledJulia_four
    (pMap m '' annW) hWo hWc hWne hWinf hfar
  have htr := bottcher_transcendental_far 4 zero_not_mem_filledJulia_four hWo hWc hWne hWinf
    hfar ha₂
  -- descend the assumed relation to compose-with-p coefficients
  set x : meroField annW :=
    (algebraMap (analyticSubring annW) (meroField annW) phiAnnAn) ^ (2 ^ (m + 1)) with hx
  have hψ : IsAlgebraic (RatFunc ℂ) x :=
    ((isAlgebraic_iff_isIntegral.mp halg).pow _).isAlgebraic
  obtain ⟨Q, hQ0, hQev⟩ := hψ
  rw [aeval_def, RingHom.algebraMap_toAlgebra] at hQev
  obtain ⟨S, hS0, hSev⟩ := descend_algebraic m x Q hQ0 hQev
  -- the pullback embedding along pMap m
  have hmaps : Set.MapsTo (pMap m) annW (pMap m '' annW) := Set.mapsTo_image _ _
  have hganal : AnalyticOnNhd ℂ (pMap m) annW := (pMap_analyticOnNhd m).mono (subset_univ _)
  have hsurj : (pMap m '' annW) ⊆ pMap m '' annW := subset_rfl
  have hpullinj : Function.Injective
      ((algebraMap (analyticSubring annW) (meroField annW)).comp (pullAn hmaps hganal)) :=
    (IsFractionRing.injective (analyticSubring annW) (meroField annW)).comp
      (pullAn_injective hmaps hganal hsurj)
  set Φ : meroField (pMap m '' annW) →+* meroField annW := IsFractionRing.lift hpullinj with hΦ
  -- κ is the pullback of the standard embedding
  have hpull_poly : ∀ a : Polynomial ℂ,
      pullAn hmaps hganal (polyToAnalytic (pMap m '' annW) a)
        = polyToAnalytic annW (a.comp (pPoly m)) := by
    intro a
    apply Subtype.ext
    rw [pullAn_coe]
    have h1 : ((polyToAnalytic (pMap m '' annW) a : analyticSubring (pMap m '' annW))
        : Germ (𝓟 (pMap m '' annW)) ℂ) = ↑(fun z => a.eval z) := rfl
    have h2 : ((polyToAnalytic annW (a.comp (pPoly m)) : analyticSubring annW)
        : Germ (𝓟 annW) ℂ) = ↑(fun z => (a.comp (pPoly m)).eval z) := rfl
    rw [h1, h2, germPullback_coe, Germ.coe_eq]
    apply eventually_principal.mpr
    intro z _
    show a.eval (pMap m z) = (a.comp (pPoly m)).eval z
    rw [eval_comp, pPoly_eval]
  have hΦρ : kappa m
      = Φ.comp (ratfuncToMero (pMap m '' annW) hWo hWc hWne hWinf) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
    apply RingHom.ext
    intro a
    show kappa m (algebraMap (Polynomial ℂ) (RatFunc ℂ) a)
      = Φ (ratfuncToMero (pMap m '' annW) hWo hWc hWne hWinf
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) a))
    rw [kappa_algebraMap, ratfuncToMero_algebraMap_polynomial]
    show polyToMero annW (a.comp (pPoly m))
      = Φ (algebraMap (analyticSubring (pMap m '' annW)) (meroField (pMap m '' annW))
          (polyToAnalytic (pMap m '' annW) a))
    rw [hΦ, IsFractionRing.lift_algebraMap]
    show polyToMero annW (a.comp (pPoly m))
      = algebraMap (analyticSubring annW) (meroField annW)
          (pullAn hmaps hganal (polyToAnalytic (pMap m '' annW) a))
    rw [hpull_poly]
    rfl
  -- the Böttcher germ pulls back to the dyadic power of the window branch
  have hx2 : Φ (algebraMap (analyticSubring (pMap m '' annW)) (meroField (pMap m '' annW)) a₂)
      = x := by
    rw [hΦ, IsFractionRing.lift_algebraMap]
    show algebraMap (analyticSubring annW) (meroField annW) (pullAn hmaps hganal a₂) = x
    rw [hx, ← map_pow]
    congr 1
    apply Subtype.ext
    rw [pullAn_coe]
    have ha₂v : (a₂ : Germ (𝓟 (pMap m '' annW)) ℂ) = ↑(bottcherCoord 4) := ha₂.symm
    rw [ha₂v, germPullback_coe]
    have h2 : ((phiAnnAn ^ (2 ^ (m + 1)) : analyticSubring annW) : Germ (𝓟 annW) ℂ)
        = ↑(phiFour ^ (2 ^ (m + 1))) := by
      rw [SubmonoidClass.coe_pow]
      show ((↑phiFour : Germ (𝓟 annW) ℂ)) ^ (2 ^ (m + 1)) = ↑(phiFour ^ (2 ^ (m + 1)))
      exact (Germ.coe_pow phiFour (2 ^ (m + 1))).symm
    rw [h2, Germ.coe_eq]
    apply eventually_principal.mpr
    intro z hz
    show bottcherCoord 4 (pMap m z) = (phiFour ^ (2 ^ (m + 1))) z
    have := phiFour_pow_pMap m hz
    rw [← this]
    rfl
  -- transport the relation and contradict the far transcendence
  have h0 : S.eval₂ (ratfuncToMero (pMap m '' annW) hWo hWc hWne hWinf)
      (algebraMap (analyticSubring (pMap m '' annW)) (meroField (pMap m '' annW)) a₂) = 0 := by
    apply Φ.injective
    rw [map_zero, hom_eval₂, ← hΦρ, hx2]
    exact hSev
  exact htr ⟨S, hS0, by rw [aeval_def, RingHom.algebraMap_toAlgebra]; exact h0⟩

end U0PhiFourDescent
