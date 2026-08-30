import GaloisForLFunctions.HTGeometry.CrossDomainSubstitution
import GaloisForLFunctions.HTGeometry.CompositionTowerCoherence
import GaloisForLFunctions.HTGeometry.AlgebraicWitness
import GaloisForLFunctions.HTGeometry.LocalInverseHypertranscendence
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicTransitivity

/-!
# One autonomous equation for a linearized tower

For a family of inner germs `g_n` into the domain of a differentially algebraic outer germ `Φ`, the
jets of the composites `Φ ∘ g_n` obey the chain-rule recursion inside the meromorphic function field
of the common source.  The transcendence bound needed by the compositional coherence theorem is
supplied by differential algebraicity of `Φ` and of the inner family's common factor, transported
along the substitution homomorphisms.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Bottcher
open scoped Differential

noncomputable section

/-! ## The chain rule for jets along an inner germ -/

/-- Differentiating a jet of the outer germ along an inner germ raises the jet order and multiplies
by the derivative of the inner germ. -/
theorem deriv_iteratedDeriv_comp {U V : Set ℂ} {Φ g : ℂ → ℂ}
    (hΦ : AnalyticOnNhd ℂ Φ V) (hg : AnalyticOnNhd ℂ g U) (hmaps : Set.MapsTo g U V) (j : ℕ) :
    Set.EqOn (deriv fun t => iteratedDeriv j Φ (g t))
      (fun t => iteratedDeriv (j + 1) Φ (g t) * deriv g t) U := by
  intro t ht
  have hout : HasDerivAt (iteratedDeriv j Φ) (iteratedDeriv (j + 1) Φ (g t)) (g t) := by
    have h := (analyticOnNhd_iteratedDeriv hΦ j (g t) (hmaps ht)).differentiableAt
    rw [iteratedDeriv_succ]
    exact h.hasDerivAt
  have hin : HasDerivAt g (deriv g t) t := (hg t ht).differentiableAt.hasDerivAt
  exact (hout.comp t hin).deriv

/-- The germ derivative of an analytic function element is the element of its derivative. -/
theorem analyticSubringDeriv_analyticFunctionElement {U : Set ℂ} (hUo : IsOpen U) (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f U) :
    analyticSubringDeriv hUo (analyticFunctionElement f hf)
      = analyticFunctionElement (deriv f) hf.deriv := rfl

/-- Two analytic functions agreeing on the domain have the same element. -/
theorem analyticFunctionElement_congr_eqOn {U : Set ℂ} {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U)
    (hg : AnalyticOnNhd ℂ g U) (h : Set.EqOn f g U) :
    analyticFunctionElement f hf = analyticFunctionElement g hg := by
  apply Subtype.ext
  exact Germ.coe_eq.mpr (eventually_principal.mpr h)

/-! ## Witness families for the jets of a differentially algebraic germ -/

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 1600000 in
/-- **All jets of a differentially algebraic analytic function are algebraic over one finite
family.**  Differential algebraicity caps the transcendence degree of the differential field it
generates, and a transcendence basis of that field witnesses every jet. -/
theorem exists_jet_algebraicWitness_family {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    (hWne : W.Nonempty) (hWinf : W.Infinite) {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f W)
    (hfDA : DifferentiallyAlgebraicOn f W) :
    letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
    letI : Algebra ℂ (meroField W) :=
      ((ratfuncToMero W hWo hWc hWne hWinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
    ∃ (p : ℕ) (b : Fin p → meroField W), ∀ j : ℕ,
      AlgebraicWitness ℂ b (analyticMeroElement (iteratedDeriv j f)
        (analyticOnNhd_iteratedDeriv hf j)) := by
  classical
  letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
  letI : Algebra (RatFunc ℂ) (meroField W) := (ratfuncToMero W hWo hWc hWne hWinf).toAlgebra
  letI : Differential (RatFunc ℂ) := GaloisForLFunctions.ratFuncCoordinateDifferential
  letI := meroFieldDifferential hWo hWc hWne
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField W) :=
    meroFieldRatFuncDifferentialAlgebra hWo hWc hWne hWinf
  letI : CharZero (meroField W) :=
    charZero_of_injective_algebraMap (algebraMap (RatFunc ℂ) (meroField W)).injective
  letI : Algebra ℂ (meroField W) :=
    ((ratfuncToMero W hWo hWc hWne hWinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
  haveI : IsScalarTower ℂ (RatFunc ℂ) (meroField W) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  set x : meroField W := analyticMeroElement f hf with hxdef
  have hxDA : DifferentialAlgebraicOver (RatFunc ℂ) x :=
    (differentialAlgebraicOver_analyticMeroElement_iff hWo hWc hWne hWinf hf).mpr hfDA
  set A : IntermediateField (RatFunc ℂ) (meroField W) :=
    differentialAdjoin (RatFunc ℂ) ({x} : Set (meroField W)) with hAdef
  have hfin : Algebra.trdeg (RatFunc ℂ) ↥A < Cardinal.aleph0 :=
    differentialAdjoin_trdeg_lt_aleph0_of_differentialAlgebraic hxDA
  letI : Algebra ℂ ↥A := ((algebraMap (RatFunc ℂ) ↥A).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
  haveI : IsScalarTower ℂ (RatFunc ℂ) ↥A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower ℂ ↥A (meroField W) := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) ↥A,
      IsScalarTower.algebraMap_apply ℂ (RatFunc ℂ) (meroField W)]
    rfl
  haveI hfaith1 : FaithfulSMul (RatFunc ℂ) ↥A :=
    (faithfulSMul_iff_algebraMap_injective (RatFunc ℂ) ↥A).mpr
      (algebraMap (RatFunc ℂ) ↥A).injective
  haveI hfaith2 : FaithfulSMul ℂ ↥A :=
    (faithfulSMul_iff_algebraMap_injective ℂ ↥A).mpr (algebraMap ℂ ↥A).injective
  have htower : Algebra.trdeg ℂ (RatFunc ℂ) + Algebra.trdeg (RatFunc ℂ) ↥A
      = Algebra.trdeg ℂ ↥A := trdeg_add_eq ℂ (RatFunc ℂ) (A := ↥A)
  have htr : Algebra.trdeg ℂ ↥A < Cardinal.aleph0 := by
    rw [← htower]
    exact Cardinal.add_lt_aleph0 trdeg_ratFunc_complex_lt_aleph0 hfin
  obtain ⟨p, b, hb⟩ := exists_finite_algebraicWitness_family (K := ℂ) (M := ↥A) htr
  refine ⟨p, fun i => ((b i : ↥A) : meroField W), fun j => ?_⟩
  have hmemA : differentialJet j x ∈ A :=
    differentialJet_mem_differentialAdjoin (RatFunc ℂ) (s := ({x} : Set (meroField W))) rfl j
  have hw := hb ⟨differentialJet j x, hmemA⟩
  have hmap := hw.map (AlgHom.restrictScalars ℂ A.val) (fun a b hab => Subtype.ext hab)
  have hjet : differentialJet j x = analyticMeroElement (iteratedDeriv j f)
      (analyticOnNhd_iteratedDeriv hf j) :=
    differentialJet_analyticMeroElement hWo hWc hWne f hf j
  rw [← hjet]
  exact hmap

/-! ## Constants and derivatives in a meromorphic field -/

/-- The scalar embedding is the constant germ. -/
theorem algebraMap_complex_eq_analyticMeroElement {W : Set ℂ} (hWo : IsOpen W)
    (hWc : IsPreconnected W) (hWne : W.Nonempty) (hWinf : W.Infinite) (c : ℂ) :
    letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
    letI : Algebra ℂ (meroField W) :=
      ((ratfuncToMero W hWo hWc hWne hWinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
    algebraMap ℂ (meroField W) c
      = analyticMeroElement (fun _ : ℂ => c) (analyticOnNhd_const (v := c)) := by
  letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
  show ratfuncToMero W hWo hWc hWne hWinf (algebraMap ℂ (RatFunc ℂ) c) = _
  rw [algebraMap_complex_meroField hWo hWc hWne hWinf c]
  rfl

/-- Germ differentiation of an analytic element is differentiation of the function. -/
theorem deriv_analyticMeroElement_open {W : Set ℂ} (hWo : IsOpen W) (hWc : IsPreconnected W)
    (hWne : W.Nonempty) (F : ℂ → ℂ) (hF : AnalyticOnNhd ℂ F W) :
    letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
    letI := meroFieldDifferential hWo hWc hWne
    Differential.deriv (analyticMeroElement F hF) = analyticMeroElement (deriv F) hF.deriv := by
  letI := Bottcher.isDomain_analyticSubring W hWo hWc hWne
  letI := meroFieldDifferential hWo hWc hWne
  show Differential.deriv
      (algebraMap (analyticSubring W) (meroField W) (analyticFunctionElement F hF)) = _
  rw [meroFieldDifferential_algebraMap hWo hWc hWne]
  rfl

/-- Two analytic functions agreeing on the domain have the same meromorphic element. -/
theorem analyticMeroElement_congr_eqOn {W : Set ℂ} {F G : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F W)
    (hG : AnalyticOnNhd ℂ G W) (h : Set.EqOn F G W) :
    analyticMeroElement F hF = analyticMeroElement G hG := by
  rw [analyticMeroElement, analyticMeroElement, analyticFunctionElement_congr_eqOn hF hG h]

/-! ## The tower theorem -/

set_option synthInstance.maxHeartbeats 800000 in
set_option maxHeartbeats 4000000 in
/-- **One autonomous equation for a linearized tower.**  If the outer germ and the inner germ are
differentially algebraic and the substitutions are faithful, then a single nonzero constant
coefficient polynomial annihilates the jets of every composite `Φ ∘ (μ_n · κ)`. -/
theorem exists_uniform_jet_relation_of_linearized_tower
    {U V : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U) (hUne : U.Nonempty) (hUinf : U.Infinite)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hVne : V.Nonempty) (hVinf : V.Infinite)
    {Φ κ : ℂ → ℂ} (hΦ : AnalyticOnNhd ℂ Φ V) (hκ : AnalyticOnNhd ℂ κ U) {μ : ℕ → ℂ}
    (hmaps : ∀ n : ℕ, Set.MapsTo (fun t => μ n * κ t) U V)
    (hfaith : ∀ n : ℕ, SubstitutionFaithful U V (fun t => μ n * κ t))
    (hΦDA : DifferentiallyAlgebraicOn Φ V) (hκDA : DifferentiallyAlgebraicOn κ U) :
    ∃ (r : ℕ) (Q : MvPolynomial (Fin (r + 1)) ℂ), Q ≠ 0 ∧
      ∀ (n : ℕ), ∀ z ∈ U, MvPolynomial.eval
        (fun k : Fin (r + 1) => iteratedDeriv (k : ℕ) (fun s => Φ (μ n * κ s)) z) Q = 0 := by
  classical
  letI := Bottcher.isDomain_analyticSubring U hUo hUc hUne
  letI := Bottcher.isDomain_analyticSubring V hVo hVc hVne
  letI : Algebra ℤ (meroField U) := Ring.toIntAlgebra _
  letI : Algebra ℂ (meroField U) :=
    ((ratfuncToMero U hUo hUc hUne hUinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
  letI : Algebra ℂ (meroField V) :=
    ((ratfuncToMero V hVo hVc hVne hVinf).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra
  letI := meroFieldDifferential hUo hUc hUne
  -- the inner maps
  set g : ℕ → ℂ → ℂ := fun n t => μ n * κ t with hgdef
  have hgan : ∀ n : ℕ, AnalyticOnNhd ℂ (g n) U := fun n => analyticOnNhd_const.mul hκ
  -- the jets of the composites and of the inner maps
  have hajan : ∀ (n j : ℕ), AnalyticOnNhd ℂ (fun t => iteratedDeriv j Φ (g n t)) U :=
    fun n j => (analyticOnNhd_iteratedDeriv hΦ j).comp (hgan n) (hmaps n)
  have hcjan : ∀ (n i : ℕ), AnalyticOnNhd ℂ (fun t => μ n * iteratedDeriv (i + 1) κ t) U :=
    fun n i => analyticOnNhd_const.mul (analyticOnNhd_iteratedDeriv hκ (i + 1))
  set a : ℕ → ℕ → meroField U := fun n j =>
    analyticMeroElement (fun t => iteratedDeriv j Φ (g n t)) (hajan n j) with hadef
  set c : ℕ → ℕ → meroField U := fun n i =>
    analyticMeroElement (fun t => μ n * iteratedDeriv (i + 1) κ t) (hcjan n i) with hcdef
  -- the chain rule
  have hderivg : ∀ n : ℕ, Set.EqOn (deriv (g n)) (fun t => μ n * deriv κ t) U := by
    intro n t ht
    exact deriv_const_mul _ ((hκ t ht).differentiableAt)
  have ha : ∀ (n j : ℕ), Differential.deriv (a n j) = a n (j + 1) * c n 0 := by
    intro n j
    rw [hadef, hcdef]
    rw [deriv_analyticMeroElement_open hUo hUc hUne]
    rw [← analyticMeroElement_mul]
    refine analyticMeroElement_congr_eqOn _ _ ?_
    intro t ht
    have h1 : deriv (fun s => iteratedDeriv j Φ (g n s)) t
        = iteratedDeriv (j + 1) Φ (g n t) * deriv (g n) t :=
      deriv_iteratedDeriv_comp hΦ (hgan n) (hmaps n) j ht
    show deriv (fun s => iteratedDeriv j Φ (g n s)) t
      = iteratedDeriv (j + 1) Φ (g n t) * (μ n * iteratedDeriv (0 + 1) κ t)
    rw [h1, hderivg n ht]
    norm_num [iteratedDeriv_one]
  have hc : ∀ (n i : ℕ), Differential.deriv (c n i) = c n (i + 1) := by
    intro n i
    rw [hcdef]
    rw [deriv_analyticMeroElement_open hUo hUc hUne]
    refine analyticMeroElement_congr_eqOn _ _ ?_
    intro t ht
    show deriv (fun s => μ n * iteratedDeriv (i + 1) κ s) t
      = μ n * iteratedDeriv (i + 1 + 1) κ t
    rw [deriv_const_mul _ ((analyticOnNhd_iteratedDeriv hκ (i + 1) t ht).differentiableAt),
      ← iteratedDeriv_succ]
  -- witness families for the two germs
  obtain ⟨pΦ, bΦ, hbΦ⟩ := exists_jet_algebraicWitness_family hVo hVc hVne hVinf hΦ hΦDA
  obtain ⟨pκ, bκ, hbκ⟩ := exists_jet_algebraicWitness_family hUo hUc hUne hUinf hκ hκDA
  -- the substitution homomorphisms as maps of complex algebras
  have hcomm : ∀ (n : ℕ) (x : ℂ),
      substMero hUo hUc hUne hVo hVc hVne (hgan n) (hmaps n) (hfaith n)
        (algebraMap ℂ (meroField V) x) = algebraMap ℂ (meroField U) x := by
    intro n x
    rw [algebraMap_complex_eq_analyticMeroElement hVo hVc hVne hVinf x,
      substMero_analyticMeroElement, algebraMap_complex_eq_analyticMeroElement hUo hUc hUne hUinf x]
    rfl
  set SA : ℕ → (meroField V →ₐ[ℂ] meroField U) := fun n =>
    { substMero hUo hUc hUne hVo hVc hVne (hgan n) (hmaps n) (hfaith n) with
      commutes' := hcomm n } with hSAdef
  have hSAinj : ∀ n : ℕ, Function.Injective (SA n) := fun n => (SA n).toRingHom.injective
  have hasubst : ∀ (n j : ℕ), a n j
      = SA n (analyticMeroElement (iteratedDeriv j Φ) (analyticOnNhd_iteratedDeriv hΦ j)) := by
    intro n j
    show analyticMeroElement (fun t => iteratedDeriv j Φ (g n t)) (hajan n j)
      = substMero hUo hUc hUne hVo hVc hVne (hgan n) (hmaps n) (hfaith n)
          (analyticMeroElement (iteratedDeriv j Φ) (analyticOnNhd_iteratedDeriv hΦ j))
    rw [substMero_analyticMeroElement]
    rfl
  -- the basis: the transported outer basis, the multiplier, the inner basis
  set d : ℕ := pΦ + (1 + pκ) with hddef
  set basis : ℕ → Fin d → meroField U := fun n =>
    Fin.append (fun i : Fin pΦ => SA n (bΦ i))
      (Fin.append (fun _ : Fin 1 => algebraMap ℂ (meroField U) (μ n)) bκ) with hbasisdef
  have hbasisΦ : ∀ (n : ℕ) (i : Fin pΦ), basis n (Fin.castAdd (1 + pκ) i) = SA n (bΦ i) := by
    intro n i
    rw [hbasisdef]
    exact Fin.append_left _ _ i
  have hbasisμ : ∀ n : ℕ,
      basis n (Fin.natAdd pΦ (Fin.castAdd pκ (0 : Fin 1))) = algebraMap ℂ (meroField U) (μ n) := by
    intro n
    show Fin.append (fun i : Fin pΦ => SA n (bΦ i))
        (Fin.append (fun _ : Fin 1 => algebraMap ℂ (meroField U) (μ n)) bκ)
        (Fin.natAdd pΦ (Fin.castAdd pκ (0 : Fin 1))) = _
    rw [Fin.append_right]
    exact Fin.append_left _ _ 0
  have hbasisκ : ∀ (n : ℕ) (i : Fin pκ), basis n (Fin.natAdd pΦ (Fin.natAdd 1 i)) = bκ i := by
    intro n i
    show Fin.append (fun i : Fin pΦ => SA n (bΦ i))
        (Fin.append (fun _ : Fin 1 => algebraMap ℂ (meroField U) (μ n)) bκ)
        (Fin.natAdd pΦ (Fin.natAdd 1 i)) = _
    rw [Fin.append_right]
    exact Fin.append_right _ _ i
  -- the outer jets are algebraic over the basis in every ultraproduct
  have hrankA : ∀ (u : Ultrafilter ℕ) (j : ℕ),
      IsAlgebraic ↥(IntermediateField.adjoin ℂ (Set.range fun k : Fin d =>
          ((fun n => basis n k : ℕ → meroField U) : Filter.Germ (u : Filter ℕ) (meroField U))))
        ((fun n => a n j : ℕ → meroField U) : Filter.Germ (u : Filter ℕ) (meroField U)) := by
    intro u j
    obtain ⟨m, P, hlead, hrel⟩ := hbΦ j
    have hcomp : ∀ n : ℕ, (basis n ∘ Fin.castAdd (1 + pκ)) = fun i => SA n (bΦ i) := by
      intro n
      funext i
      exact hbasisΦ n i
    refine isAlgebraic_of_algebraicWitness ?_
    refine algebraicWitness_germ u (m := m)
      (P := fun i => MvPolynomial.rename (Fin.castAdd (1 + pκ)) (P i)) ?_ ?_
    · intro n
      rw [MvPolynomial.aeval_rename, hcomp n, ← MvPolynomial.comp_aeval_apply bΦ (SA n)]
      intro h0
      exact hlead (hSAinj n (by rw [h0, map_zero]))
    · intro n
      have hmapped := congrArg (SA n) hrel
      rw [map_zero, map_sum] at hmapped
      rw [hasubst n j]
      refine Eq.trans ?_ hmapped
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [MvPolynomial.aeval_rename, hcomp n, map_mul, map_pow,
        MvPolynomial.comp_aeval_apply bΦ (SA n)]
  -- the inner jets, times the multiplier, are algebraic over the basis
  have hcmul : ∀ (n i : ℕ), c n i = algebraMap ℂ (meroField U) (μ n)
      * analyticMeroElement (iteratedDeriv (i + 1) κ)
          (analyticOnNhd_iteratedDeriv hκ (i + 1)) := by
    intro n i
    rw [algebraMap_complex_eq_analyticMeroElement hUo hUc hUne hUinf, ← analyticMeroElement_mul]
  have hrankC : ∀ (u : Ultrafilter ℕ) (i : ℕ),
      IsAlgebraic ↥(IntermediateField.adjoin ℂ (Set.range fun k : Fin d =>
          ((fun n => basis n k : ℕ → meroField U) : Filter.Germ (u : Filter ℕ) (meroField U))))
        ((fun n => c n i : ℕ → meroField U) : Filter.Germ (u : Filter ℕ) (meroField U)) := by
    intro u i
    have hsplit : ((fun n => c n i : ℕ → meroField U) : Filter.Germ (u : Filter ℕ) (meroField U))
        = ((fun n => algebraMap ℂ (meroField U) (μ n) : ℕ → meroField U) :
            Filter.Germ (u : Filter ℕ) (meroField U))
          * ((fun _ : ℕ => analyticMeroElement (iteratedDeriv (i + 1) κ)
              (analyticOnNhd_iteratedDeriv hκ (i + 1)) : ℕ → meroField U) :
            Filter.Germ (u : Filter ℕ) (meroField U)) := by
      rw [← Filter.Germ.coe_mul]
      congr 1
      funext n
      exact hcmul n i
    rw [hsplit]
    refine IsAlgebraic.mul ?_ ?_
    · have hmem : ((fun n => algebraMap ℂ (meroField U) (μ n) : ℕ → meroField U) :
          Filter.Germ (u : Filter ℕ) (meroField U))
          ∈ IntermediateField.adjoin ℂ (Set.range fun k : Fin d =>
            ((fun n => basis n k : ℕ → meroField U) :
              Filter.Germ (u : Filter ℕ) (meroField U))) := by
        refine IntermediateField.subset_adjoin ℂ _ ⟨Fin.natAdd pΦ (Fin.castAdd pκ (0 : Fin 1)), ?_⟩
        show ((fun n => basis n (Fin.natAdd pΦ (Fin.castAdd pκ (0 : Fin 1))) : ℕ → meroField U) :
            Filter.Germ (u : Filter ℕ) (meroField U)) = _
        congr 1
        funext n
        exact hbasisμ n
      exact isAlgebraic_algebraMap (R := ↥(IntermediateField.adjoin ℂ _)) ⟨_, hmem⟩
    · obtain ⟨m, P, hlead, hrel⟩ := hbκ (i + 1)
      have hcomp : ∀ n : ℕ,
          (basis n ∘ fun k : Fin pκ => Fin.natAdd pΦ (Fin.natAdd 1 k)) = bκ := by
        intro n
        funext k
        exact hbasisκ n k
      refine isAlgebraic_of_algebraicWitness ?_
      refine algebraicWitness_germ u (m := m)
        (P := fun l => MvPolynomial.rename (fun k : Fin pκ => Fin.natAdd pΦ (Fin.natAdd 1 k))
          (P l)) ?_ ?_
      · intro n
        rw [MvPolynomial.aeval_rename, hcomp n]
        exact hlead
      · intro n
        refine Eq.trans ?_ hrel
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [MvPolynomial.aeval_rename, hcomp n]
  -- the derivation kills the constants
  have hKconst : ∀ x : ℂ, Differential.deriv (algebraMap ℂ (meroField U) x) = 0 := by
    intro x
    rw [algebraMap_complex_eq_analyticMeroElement hUo hUc hUne hUinf x,
      deriv_analyticMeroElement_open hUo hUc hUne]
    have hz : Set.EqOn (deriv fun _ : ℂ => x) (fun _ : ℂ => (0 : ℂ)) U := by
      intro t _
      simp
    rw [analyticMeroElement_congr_eqOn _ (analyticOnNhd_const (v := (0 : ℂ))) hz]
    show algebraMap (analyticSubring U) (meroField U)
      (analyticFunctionElement (fun _ : ℂ => (0 : ℂ)) analyticOnNhd_const) = 0
    rw [show analyticFunctionElement (fun _ : ℂ => (0 : ℂ)) analyticOnNhd_const = 0 from rfl,
      map_zero]
  obtain ⟨Q, hQ0, hQ⟩ := exists_uniform_annihilator_of_composition_rank
    (Differential.deriv) hKconst a c basis ha hc hrankA hrankC
  refine ⟨d, Q, hQ0, ?_⟩
  intro n z hz
  have hjet : ∀ k : ℕ, (⇑(Differential.deriv : Derivation ℤ (meroField U) (meroField U)))^[k]
      (a n 0) = analyticMeroElement (iteratedDeriv k (fun s => Φ (μ n * κ s)))
        (analyticOnNhd_iteratedDeriv (hajan n 0) k) := by
    intro k
    have h0 : a n 0 = analyticMeroElement (fun s => Φ (μ n * κ s)) (hajan n 0) := rfl
    rw [h0]
    exact differentialJet_analyticMeroElement hUo hUc hUne _ (hajan n 0) k
  have hfin := hQ n
  rw [show (fun k : Fin (d + 1) =>
      (⇑(Differential.deriv : Derivation ℤ (meroField U) (meroField U)))^[(k : ℕ)] (a n 0))
      = fun k : Fin (d + 1) => analyticMeroElement
        (iteratedDeriv (k : ℕ) (fun s => Φ (μ n * κ s)))
        (analyticOnNhd_iteratedDeriv (hajan n 0) (k : ℕ)) from funext fun k => hjet k] at hfin
  exact (aeval_analyticMeroElement_eq_zero_iff hUo hUc hUne hUinf
    (fun k : Fin (d + 1) => iteratedDeriv (k : ℕ) (fun s => Φ (μ n * κ s)))
    (fun k => analyticOnNhd_iteratedDeriv (hajan n 0) (k : ℕ)) Q).mp hfin z hz

end

end GaloisForLFunctions.HTGeometry
