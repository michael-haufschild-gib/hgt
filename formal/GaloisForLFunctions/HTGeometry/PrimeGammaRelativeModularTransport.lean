import GaloisForLFunctions.HTGeometry.PrimeGammaFrameInjective
import GaloisForLFunctions.HTGeometry.InjectiveDenseRangePolarUnitary
import GaloisForLFunctions.HTGeometry.MaximalComplexL2Multiplication
import GaloisForLFunctions.HTGeometry.SourceGaugeObservabilitySpectrum
import GaloisForLFunctions.HTGeometry.WeightedOrbitSelectionLaw
import GaloisForLFunctions.RHTower.GammaRCubeThetaPairsL2
import GaloisForLFunctions.RHTower.SchattenApproximation

/-!
# Relative nuclear modular transport of the prime formation frames

Let `𝓜` be the Mellin unitary of `L²((0,∞), dr)`, `𝓜 f(ξ) = mellin f (1/2 - 2πiξ)`, and let
`A_∞ = 𝓜⁻¹ M_a 𝓜` be the closed multiplier with the relative Gamma symbol
`a(s) = Γ(s+1)/Γ(s+1/2)` on the unitary axis.  It is injective, and it carries every degree-two
coherent vector to its degree-three partner.  Since it is closed, the finite-packet identity
passes to the whole prime coefficient space:

* **(PPTI.35)** `A_∞ W_d^{(2)} = W_d^{(3)}` on all of `ℓ²(Primes)`;
* **(PPTI.37)–(PPTI.38)** both frames are injective with dense range, so their left polar
  factors `W^{(k)} = (B^{(k)})^{1/2} V_k` are unitary and `U_∞ = V_3 V_2*` is a unitary of `H`;
* **(PPTI.39)–(PPTI.40)** `A_∞ (B^{(2)})^{1/2} = (B^{(3)})^{1/2} U_∞`, and `U_∞ h` is the unique
  vector `g` with `A_∞ (B^{(2)})^{1/2} h = (B^{(3)})^{1/2} g`.

The left Grams `B^{(k)}` are compact and injective on the infinite-dimensional `H`, so their
dense ranges are not closed and their inverses are unbounded (PPTI.33).
-/

open MeasureTheory Set Filter Topology Complex
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## Graphs of unitary conjugates -/

theorem mem_graph_unitaryConjugateLinearPMap_iff {H K : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (f g : H) :
    (f, g) ∈ (unitaryConjugateLinearPMap U T).graph ↔ (U f, U g) ∈ T.graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x, hx, hval⟩
    refine ⟨unitaryConjugateDomainMap U T x, congrArg U hx, ?_⟩
    change U.symm (T (unitaryConjugateDomainMap U T x)) = g at hval
    change T (unitaryConjugateDomainMap U T x) = U g
    rw [← hval, LinearIsometryEquiv.apply_symm_apply]
  · rintro ⟨x, hx, hval⟩
    let xU : (unitaryConjugateLinearPMap U T).domain :=
      ⟨U.symm x, by
        change U (U.symm (x : K)) ∈ T.domain
        simpa only [LinearIsometryEquiv.apply_symm_apply] using x.property⟩
    have hxdom : unitaryConjugateDomainMap U T xU = x := by
      apply Subtype.ext
      simp only [unitaryConjugateDomainMap, LinearMap.coe_mk, AddHom.coe_mk, xU,
        LinearIsometryEquiv.apply_symm_apply]
    refine ⟨xU, ?_, ?_⟩
    · change U.symm (x : K) = f
      rw [show (x : K) = U f from hx, LinearIsometryEquiv.symm_apply_apply]
    · change U.symm (T (unitaryConjugateDomainMap U T xU)) = g
      rw [hxdom, show T x = U g from hval, LinearIsometryEquiv.symm_apply_apply]

/-! ## The Mellin creator -/

/-- The relative creator on the unitary Mellin axis, `ξ ↦ a(1/2 - 2πiξ)`. -/
def relativeCreatorSymbol (ξ : ℝ) : ℂ :=
  mellinRelativeCreator (1 / 2 - 2 * Real.pi * ξ * Complex.I)

theorem relativeCreatorSymbol_ne_zero (ξ : ℝ) : relativeCreatorSymbol ξ ≠ 0 := by
  rw [relativeCreatorSymbol, mellinRelativeCreator]
  refine div_ne_zero (Complex.Gamma_ne_zero_of_re_pos ?_) (Complex.Gamma_ne_zero_of_re_pos ?_)
  · simp only [add_re, sub_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, one_re, div_ofNat_re]
    norm_num
  · simp only [add_re, sub_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, one_re, div_ofNat_re]
    norm_num

/-- **The relative Mellin creator** `A_∞ = 𝓜⁻¹ M_a 𝓜`. -/
def mellinCreatorOp : HalfLineL2 →ₗ.[ℂ] HalfLineL2 :=
  unitaryConjugateLinearPMap halfLineMellinUnitary
    (maximalComplexL2Mul volume relativeCreatorSymbol)

theorem mem_graph_mellinCreatorOp_iff (f g : HalfLineL2) :
    (f, g) ∈ mellinCreatorOp.graph ↔
      (halfLineMellinUnitary g : ℝ → ℂ) =ᵐ[volume]
        fun ξ => relativeCreatorSymbol ξ * (halfLineMellinUnitary f : ℝ → ℂ) ξ := by
  rw [mellinCreatorOp, mem_graph_unitaryConjugateLinearPMap_iff,
    mem_graph_maximalComplexL2Mul_iff]

/-- `A_∞` is closed. -/
theorem mellinCreatorOp_isClosed : mellinCreatorOp.IsClosed :=
  LinearPMap.IsClosed.unitaryConjugate maximalComplexL2Mul_isClosed

/-- `A_∞` is injective. -/
theorem mellinCreatorOp_eq_zero_iff (f : mellinCreatorOp.domain) :
    mellinCreatorOp f = 0 ↔ (f : HalfLineL2) = 0 := by
  constructor
  · intro hf
    have hgraph : ((f : HalfLineL2), (0 : HalfLineL2)) ∈ mellinCreatorOp.graph := by
      rw [← hf]
      exact mellinCreatorOp.mem_graph f
    rw [mem_graph_mellinCreatorOp_iff, map_zero] at hgraph
    apply halfLineMellinUnitary.injective
    rw [map_zero]
    refine Lp.ext ?_
    filter_upwards [hgraph, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with ξ hξ hz
    rw [hz] at hξ ⊢
    exact (mul_eq_zero.1 hξ.symm).resolve_left (relativeCreatorSymbol_ne_zero ξ)
  · intro hf
    have hf0 : f = 0 := Subtype.ext hf
    rw [hf0]
    exact mellinCreatorOp.toFun.map_zero

/-! ## The coherent vectors in Mellin coordinates -/

theorem mellinConvergent_gammaCoherentProfile {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : 0 < t) :
    MellinConvergent (fun r => (gammaCoherentProfile k t r : ℂ)) ((1 / 2 : ℝ) : ℂ) := by
  set α : ℝ := ((k : ℝ) - 1) / 2
  set C : ℝ := Real.sqrt ((2 * t) ^ k / ((k - 1).factorial : ℝ))
  have hcongr : EqOn (fun r => (gammaCoherentProfile k t r : ℂ))
      (fun r => (C : ℂ) • ((r : ℂ) ^ (α : ℂ) • ((Real.exp (-(t * r)) : ℝ) : ℂ))) (Ioi 0) := by
    intro r hr
    simp only [gammaCoherentProfile, smul_eq_mul]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt hr)]
    ring
  have hre : 0 < (((1 / 2 : ℝ) : ℂ) + (α : ℂ)).re := by
    simp only [add_re, ofReal_re, α]
    have : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk
    linarith
  have hbase : MellinConvergent (fun r : ℝ => ((Real.exp (-r) : ℝ) : ℂ))
      (((1 / 2 : ℝ) : ℂ) + (α : ℂ)) := by
    refine (Complex.GammaIntegral_convergent hre).congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp only [smul_eq_mul]
    ring
  have h1 : MellinConvergent (fun r : ℝ => ((Real.exp (-(t * r)) : ℝ) : ℂ))
      (((1 / 2 : ℝ) : ℂ) + (α : ℂ)) :=
    (MellinConvergent.comp_mul_left (f := fun r : ℝ => ((Real.exp (-r) : ℝ) : ℂ)) ht).2 hbase
  have h2 := (MellinConvergent.cpow_smul (a := (α : ℂ))).2 h1
  have h3 := h2.const_smul (C : ℂ)
  refine h3.congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp only [hcongr hr]

theorem halfLineMellinUnitary_gammaCoherentVector (k : ℕ) [NeZero k] {t : ℝ} (ht : 0 < t) :
    (halfLineMellinUnitary (gammaCoherentVector k ht) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => mellin (fun r => (gammaCoherentProfile k t r : ℂ))
        (1 / 2 - 2 * Real.pi * ξ * Complex.I) :=
  halfLineMellinUnitary_ae_eq_mellin _ _ (gammaCoherentVector_ae k ht)
    (integrable_halfDensityPullback_of_mellinConvergent
      (mellinConvergent_gammaCoherentProfile (NeZero.ne k) ht))

/-- **(PPTI.25) as an operator identity.**  `A_∞ ψ_t^{(2)} = ψ_t^{(3)}`. -/
theorem gammaCoherent_mem_graph_mellinCreatorOp {t : ℝ} (ht : 0 < t) :
    (gammaCoherentVector 2 ht, gammaCoherentVector 3 ht) ∈ mellinCreatorOp.graph := by
  rw [mem_graph_mellinCreatorOp_iff]
  filter_upwards [halfLineMellinUnitary_gammaCoherentVector 2 ht,
    halfLineMellinUnitary_gammaCoherentVector 3 ht] with ξ h2 h3
  rw [h3, h2, relativeCreatorSymbol]
  refine mellin_gammaCoherent_three_eq ht ?_
  simp only [sub_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, one_re, div_ofNat_re]
  norm_num

/-! ## The whole prime coefficient space -/

variable {d : ℝ}

theorem dense_span_lp_single {ι : Type*} [DecidableEq ι] :
    (Submodule.span ℂ (Set.range fun i : ι => (lp.single 2 i (1 : ℂ) :
      lp (fun _ : ι => ℂ) 2))).topologicalClosure = ⊤ := by
  have := (HilbertSchmidt.lpBasis ι).dense_span
  rwa [show (⇑(HilbertSchmidt.lpBasis ι)) = fun j => (lp.single 2 j (1 : ℂ) :
    lp (fun _ : ι => ℂ) 2) from funext HilbertSchmidt.lpBasis_apply] at this

/-- **(PPTI.35).**  `A_∞ W_d^{(2)} c = W_d^{(3)} c` for every `c ∈ ℓ²(Primes)`. -/
theorem primeCoherentSynthesis_mem_graph (hd : 0 < d) (c : lp (fun _ : Nat.Primes => ℂ) 2) :
    (primeCoherentSynthesis 2 hd c, primeCoherentSynthesis 3 hd c) ∈ mellinCreatorOp.graph := by
  let P : lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] HalfLineL2 × HalfLineL2 :=
    (primeCoherentSynthesis 2 hd).prod (primeCoherentSynthesis 3 hd)
  let S : Submodule ℂ (lp (fun _ : Nat.Primes => ℂ) 2) :=
    mellinCreatorOp.graph.comap (P : lp (fun _ : Nat.Primes => ℂ) 2 →ₗ[ℂ] _)
  have hclosed : IsClosed (S : Set (lp (fun _ : Nat.Primes => ℂ) 2)) :=
    mellinCreatorOp_isClosed.preimage P.continuous
  have hspan : Submodule.span ℂ (Set.range fun p : Nat.Primes =>
      (lp.single 2 p (1 : ℂ) : lp (fun _ : Nat.Primes => ℂ) 2)) ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    change (primeCoherentSynthesis 2 hd (lp.single 2 p 1),
      primeCoherentSynthesis 3 hd (lp.single 2 p 1)) ∈ mellinCreatorOp.graph
    rw [primeCoherentSynthesis_single, primeCoherentSynthesis_single, primeCoherentFrame,
      primeCoherentFrame]
    exact mellinCreatorOp.graph.smul_mem ((Real.sqrt (primeFormationLaw d p) : ℝ) : ℂ)
      (gammaCoherent_mem_graph_mellinCreatorOp (primeClock_pos p))
  have htop : S = ⊤ := eq_top_iff.2 (dense_span_lp_single.symm.le.trans
    (Submodule.topologicalClosure_minimal _ hspan hclosed))
  have hc : c ∈ S := htop ▸ Submodule.mem_top
  exact hc

theorem mellinCreatorOp_primeCoherentSynthesis (hd : 0 < d)
    (c : lp (fun _ : Nat.Primes => ℂ) 2) :
    ∃ h : primeCoherentSynthesis 2 hd c ∈ mellinCreatorOp.domain,
      mellinCreatorOp ⟨_, h⟩ = primeCoherentSynthesis 3 hd c := by
  obtain ⟨y, hy, hval⟩ := (LinearPMap.mem_graph_iff _).1 (primeCoherentSynthesis_mem_graph hd c)
  have hy' : (y : HalfLineL2) = primeCoherentSynthesis 2 hd c := hy
  refine ⟨hy' ▸ y.property, ?_⟩
  have hyz : (⟨primeCoherentSynthesis 2 hd c, hy' ▸ y.property⟩ : mellinCreatorOp.domain) = y :=
    Subtype.ext hy'.symm
  rw [hyz]
  exact hval

/-- **(PPTI.36).**  Both prime frames are injective. -/
theorem ker_primeCoherentSynthesis_two_eq_three (hd : 0 < d) :
    LinearMap.ker (primeCoherentSynthesis 2 hd : lp (fun _ : Nat.Primes => ℂ) 2 →ₗ[ℂ] HalfLineL2) =
      LinearMap.ker
        (primeCoherentSynthesis 3 hd : lp (fun _ : Nat.Primes => ℂ) 2 →ₗ[ℂ] HalfLineL2) := by
  rw [LinearMap.ker_eq_bot.2 (primeCoherentSynthesis_injective 2 hd),
    LinearMap.ker_eq_bot.2 (primeCoherentSynthesis_injective 3 hd)]

theorem denseRange_primeCoherentSynthesis (k : ℕ) [NeZero k] (hd : 0 < d) :
    DenseRange (primeCoherentSynthesis k hd) := by
  have hspan : Submodule.span ℂ (Set.range (primeCoherentFrame k d)) ≤
      LinearMap.range ((primeCoherentSynthesis k hd : _ →L[ℂ] HalfLineL2) :
        lp (fun _ : Nat.Primes => ℂ) 2 →ₗ[ℂ] HalfLineL2) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨p, rfl⟩
    exact ⟨lp.single 2 p 1, primeCoherentSynthesis_single k hd p⟩
  have htop := eq_top_iff.2 ((primeCoherentFrame_total k hd).symm.le.trans
    (Submodule.topologicalClosure_mono hspan))
  have hrange : Set.range ⇑(primeCoherentSynthesis k hd) =
      (LinearMap.range ((primeCoherentSynthesis k hd : _ →L[ℂ] HalfLineL2) :
        lp (fun _ : Nat.Primes => ℂ) 2 →ₗ[ℂ] HalfLineL2) : Set HalfLineL2) :=
    (LinearMap.coe_range _).symm
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top]
  exact htop

/-! ## Polar factors and the relative modular unitary -/

/-- The unitary left polar factor `V_k` of `W_d^{(k)} = (B_d^{(k)})^{1/2} V_k`. -/
def primeFormationPolar (k : ℕ) [NeZero k] (hd : 0 < d) :
    lp (fun _ : Nat.Primes => ℂ) 2 ≃ₗᵢ[ℂ] HalfLineL2 :=
  polarUnitary (primeCoherentSynthesis k hd) (primeCoherentSynthesis_injective k hd)
    (denseRange_primeCoherentSynthesis k hd)

/-- The left modulus is the positive square root of the left Gram `B_d^{(k)}`. -/
theorem leftModulus_primeCoherentSynthesis (k : ℕ) [NeZero k] (hd : 0 < d) :
    (leftModulus (primeCoherentSynthesis k hd)).IsPositive ∧
      leftModulus (primeCoherentSynthesis k hd) ∘L leftModulus (primeCoherentSynthesis k hd) =
        primeCoherentSynthesis k hd ∘L ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd) :=
  ⟨isPositive_leftModulus _, leftModulus_comp_self _⟩

/-- **(PPTI.37).**  `W_d^{(k)} = (B_d^{(k)})^{1/2} V_k`. -/
theorem leftModulus_primeFormationPolar (k : ℕ) [NeZero k] (hd : 0 < d)
    (c : lp (fun _ : Nat.Primes => ℂ) 2) :
    leftModulus (primeCoherentSynthesis k hd) (primeFormationPolar k hd c) =
      primeCoherentSynthesis k hd c :=
  leftModulus_polarUnitary _ _ _ c

/-- The polar factor is the unique unitary with `W = (B)^{1/2} V`. -/
theorem primeFormationPolar_unique (k : ℕ) [NeZero k] (hd : 0 < d)
    (V : lp (fun _ : Nat.Primes => ℂ) 2 ≃ₗᵢ[ℂ] HalfLineL2)
    (hV : ∀ c, leftModulus (primeCoherentSynthesis k hd) (V c) = primeCoherentSynthesis k hd c) :
    V = primeFormationPolar k hd :=
  polarUnitary_unique _ _ _ V hV

/-- **(PPTI.38).**  The relative modular unitary `U_∞ = V_3 V_2*`. -/
def relativeModularUnitary (hd : 0 < d) : HalfLineL2 ≃ₗᵢ[ℂ] HalfLineL2 :=
  (primeFormationPolar 2 hd).symm.trans (primeFormationPolar 3 hd)

theorem relativeModularUnitary_apply (hd : 0 < d) (h : HalfLineL2) :
    relativeModularUnitary hd h = primeFormationPolar 3 hd ((primeFormationPolar 2 hd).symm h) :=
  rfl

/-- **(PPTI.39).**  `A_∞ (B^{(2)})^{1/2} = (B^{(3)})^{1/2} U_∞` on the whole space. -/
theorem leftModulus_mem_graph_mellinCreatorOp (hd : 0 < d) (h : HalfLineL2) :
    (leftModulus (primeCoherentSynthesis 2 hd) h,
      leftModulus (primeCoherentSynthesis 3 hd) (relativeModularUnitary hd h)) ∈
        mellinCreatorOp.graph := by
  have hmem := primeCoherentSynthesis_mem_graph hd ((primeFormationPolar 2 hd).symm h)
  rwa [← leftModulus_primeFormationPolar 3 hd, primeFormationPolar,
    apply_polarUnitary_symm] at hmem

/-- **(PPTI.40).**  `(B^{(3)})^{-1/2} A_∞ (B^{(2)})^{1/2} = U_∞`: the vector `g` satisfies
`A_∞ (B^{(2)})^{1/2} h = (B^{(3)})^{1/2} g` exactly when `g = U_∞ h`. -/
theorem mem_graph_leftModulus_iff (hd : 0 < d) (h g : HalfLineL2) :
    (leftModulus (primeCoherentSynthesis 2 hd) h, leftModulus (primeCoherentSynthesis 3 hd) g) ∈
        mellinCreatorOp.graph ↔ g = relativeModularUnitary hd h := by
  constructor
  · intro hg
    exact injective_leftModulus (denseRange_primeCoherentSynthesis 3 hd)
      (mellinCreatorOp.mem_graph_snd_inj hg (leftModulus_mem_graph_mellinCreatorOp hd h) rfl)
  · rintro rfl
    exact leftModulus_mem_graph_mellinCreatorOp hd h

/-- `U_∞` is the unique unitary whitening the creator. -/
theorem relativeModularUnitary_unique (hd : 0 < d) (U : HalfLineL2 ≃ₗᵢ[ℂ] HalfLineL2)
    (hU : ∀ h, (leftModulus (primeCoherentSynthesis 2 hd) h,
      leftModulus (primeCoherentSynthesis 3 hd) (U h)) ∈ mellinCreatorOp.graph) :
    U = relativeModularUnitary hd := by
  exact LinearIsometryEquiv.ext fun h => (mem_graph_leftModulus_iff hd h (U h)).1 (hU h)

/-! ## The left Grams have dense nonclosed range -/

theorem not_finiteDimensional_halfLineL2 : ¬ FiniteDimensional ℂ HalfLineL2 := by
  intro hfin
  have hinj := primeCoherentSynthesis_injective 2 (d := 1) one_pos
  have hP : Module.Finite ℂ (lp (fun _ : Nat.Primes => ℂ) 2) :=
    Module.Finite.of_injective ((primeCoherentSynthesis 2 (d := 1) one_pos :
      lp (fun _ : Nat.Primes => ℂ) 2 →L[ℂ] HalfLineL2) :
        lp (fun _ : Nat.Primes => ℂ) 2 →ₗ[ℂ] HalfLineL2) hinj
  exact not_finiteDimensional_lp (I := Nat.Primes) (H := ℂ) hP

/-- **(PPTI.33).**  The faithful nuclear left Gram `B_d^{(k)}` has dense but nonclosed range. -/
theorem not_isClosed_range_primeFormationLeftGram (k : ℕ) [NeZero k] (hd : 0 < d) :
    ¬ IsClosed (Set.range (primeCoherentSynthesis k hd ∘L
      ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd))) := by
  intro hclosed
  obtain ⟨-, hS, -, hinj, -⟩ := primeFormationLeftGram_properties k hd
  exact not_finiteDimensional_halfLineL2
    (finiteDimensional_of_compact_injective_isClosed_range _
      (hS.isCompactOperator one_pos) hinj hclosed)

/-- The inverse of `B_d^{(k)}` is unbounded: no estimate `‖h‖ ≤ C ‖B h‖` holds. -/
theorem not_exists_bound_primeFormationLeftGram (k : ℕ) [NeZero k] (hd : 0 < d) :
    ¬ ∃ C : ℝ, ∀ h : HalfLineL2, ‖h‖ ≤ C * ‖(primeCoherentSynthesis k hd ∘L
      ContinuousLinearMap.adjoint (primeCoherentSynthesis k hd)) h‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨-, -, -, hinj, -⟩ := primeFormationLeftGram_properties k hd
  refine not_isClosed_range_primeFormationLeftGram k hd
    ((ContinuousLinearMap.isClosed_range_iff_antilipschitz_of_injective _ hinj).2
      ⟨⟨max C 0, le_max_right _ _⟩, ContinuousLinearMap.antilipschitz_of_bound _ fun h => ?_⟩)
  exact (hC h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

end GaloisForLFunctions.HTGeometry
