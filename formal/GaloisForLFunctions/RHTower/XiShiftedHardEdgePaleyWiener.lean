import GaloisForLFunctions.RHTower.XiShiftedHardEdgeDerivativeBound
import GaloisForLFunctions.RHTower.XiShiftedHardEdgePrecompactness
import GaloisForLFunctions.HTGeometry.L2DerivativeFourier
import GaloisForLFunctions.HTGeometry.PoissonKernelIntegrals

/-!
# Paley–Wiener support of a strong limit of rational hard-edge tests

The Cayley lift of a trigonometric profile lies in `L²` because the half-density factor is
`a/√(a²+x²)`, and the whole chain of its spectral derivatives is again of this shape.  Feeding that
chain into the `L²` Fourier multiplier calculus turns the trigonometric derivative bound

`‖g^{(m)}‖₂ ≤ (∏_{i<m} (1/a)(1/2 + 2(N+i)))·‖g‖₂`

into a frequency-tail bound for `ĝ`, and along a family with `N ≤ Ca` and `a → ∞` the constant
tends to `(2C)^m`.  Letting `m` grow kills every frequency with `2π|ξ| > 2C`: the strong limit is a
Paley–Wiener function of exponential type `2C`.
-/

open MeasureTheory Filter FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The Cayley lift as an `L²` function -/

theorem continuous_routeUCayleyLift (a : ℝ) {F : ℝ → ℝ} (hF : Continuous F) :
    Continuous (routeUCayleyLift a F) := by
  unfold routeUCayleyLift routeUHardEdgeInverseChart
  fun_prop

theorem memLp_routeUCayleyLift {a : ℝ} (ha : 0 < a) {F : ℝ → ℝ} (hF : Continuous F)
    {M : ℝ} (hM : ∀ θ : ℝ, |F θ| ≤ M) :
    MemLp (routeUCayleyLift a F) 2 (volume : Measure ℝ) := by
  have hcont := continuous_routeUCayleyLift a hF
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  have hdom : Integrable (fun x : ℝ => M ^ 2 * a ^ 2 * ((a ^ 2 + x ^ 2)⁻¹))
      (volume : Measure ℝ) := (integrable_inv_sq_add_sq ha).const_mul _
  refine Integrable.mono' hdom (hcont.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hpos : (0 : ℝ) < a ^ 2 + x ^ 2 := by positivity
  have hsq : routeUCayleyLift a F x ^ 2
      = (a ^ 2 / (a ^ 2 + x ^ 2)) * F (routeUHardEdgeInverseChart a x) ^ 2 := by
    rw [routeUCayleyLift, mul_pow, cos_half_inverseChart_sq ha]
  have hFb : F (routeUHardEdgeInverseChart a x) ^ 2 ≤ M ^ 2 := by
    have h := hM (routeUHardEdgeInverseChart a x)
    nlinarith [abs_nonneg (F (routeUHardEdgeInverseChart a x)),
      sq_abs (F (routeUHardEdgeInverseChart a x))]
  have hfrac : (0 : ℝ) ≤ a ^ 2 / (a ^ 2 + x ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hsq]
  refine le_trans (mul_le_mul_of_nonneg_left hFb hfrac) (le_of_eq ?_)
  field_simp

/-! ## The complexified derivative chain -/

/-- The complexified chain of spectral derivatives of a Cayley lift. -/
def routeUCayleyChain (a : ℝ) (F : ℝ → ℝ) (j : ℕ) (x : ℝ) : ℂ :=
  ((routeUCayleyLift a (trigCayleyIter a j F) x : ℝ) : ℂ)

theorem memLp_routeUCayleyChain {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (j : ℕ) :
    MemLp (routeUCayleyChain a F j) 2 (volume : Measure ℝ) := by
  have hiter : RealTrigDeg (D + j) (trigCayleyIter a j F) := realTrigDeg_trigCayleyIter j D hF
  obtain ⟨M, hM⟩ := hiter.exists_bound
  exact memLp_ofReal (memLp_routeUCayleyLift ha hiter.continuous hM)

theorem hasDerivAt_routeUCayleyChain {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (j : ℕ) (x : ℝ) :
    HasDerivAt (routeUCayleyChain a F j) (routeUCayleyChain a F (j + 1) x) x := by
  have hiter : RealTrigDeg (D + j) (trigCayleyIter a j F) := realTrigDeg_trigCayleyIter j D hF
  have hstep := hasDerivAt_routeUCayleyLift_step ha (F := trigCayleyIter a j F)
    (F' := deriv (trigCayleyIter a j F)) (fun θ => hiter.hasDerivAt θ) x
  have hnext : routeUCayleyChain a F (j + 1) x
      = ((routeUCayleyLift a (trigCayleyStep a (trigCayleyIter a j F)
          (deriv (trigCayleyIter a j F))) x : ℝ) : ℂ) := by
    rw [routeUCayleyChain, trigCayleyIter_succ]
  rw [hnext]
  exact hstep.ofReal_comp

theorem norm_toLp_routeUCayleyChain_sq {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (j : ℕ) :
    ‖(memLp_routeUCayleyChain ha hF j).toLp (routeUCayleyChain a F j)‖ ^ 2
      = ∫ x : ℝ, routeUCayleyLift a (trigCayleyIter a j F) x ^ 2 := by
  rw [norm_lpTwo_sq]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_routeUCayleyChain ha hF j).coeFn_toLp] with x hx
  rw [hx, routeUCayleyChain, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## The frequency tail of a single packet -/

/-- The trigonometric derivative bound transported to the `L²` classes of the chain. -/
theorem norm_toLp_routeUCayleyChain_le {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) (m : ℕ) :
    ‖(memLp_routeUCayleyChain ha hF m).toLp (routeUCayleyChain a F m)‖
      ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))))
        * ‖(memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)‖ := by
  have hP : (0 : ℝ) ≤ ∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))) := by
    refine Finset.prod_nonneg fun i _ => ?_
    have h1 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
    have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    have h3 : (0 : ℝ) < 1 / a := by positivity
    nlinarith
  have hbase := integral_iteratedDeriv_routeUCayleyLift_sq_le ha m hF
  rw [iteratedDeriv_routeUCayleyLift ha m hF] at hbase
  have hsq : ‖(memLp_routeUCayleyChain ha hF m).toLp (routeUCayleyChain a F m)‖ ^ 2
      ≤ ((∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))))
        * ‖(memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)‖) ^ 2 := by
    rw [mul_pow, norm_toLp_routeUCayleyChain_sq ha hF m, norm_toLp_routeUCayleyChain_sq ha hF 0,
      trigCayleyIter_zero]
    exact hbase
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **The frequency-tail estimate for a single hard-edge packet.** -/
theorem routeUCayley_highFrequency_le {a : ℝ} (ha : 0 < a) {D : ℕ} {F : ℝ → ℝ}
    (hF : RealTrigDeg D F) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    r ^ m * ‖restrictLp (highFrequencySet r)
        (𝓕 ((memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)))‖
      ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((D : ℝ) + (i : ℝ))))
        * ‖(memLp_routeUCayleyChain ha hF 0).toLp (routeUCayleyChain a F 0)‖ :=
  le_trans
    (norm_restrictLp_fourier_le (f := routeUCayleyChain a F)
      (fun j => memLp_routeUCayleyChain ha hF j)
      (fun j x => hasDerivAt_routeUCayleyChain ha hF j x) hr m)
    (norm_toLp_routeUCayleyChain_le ha hF m)


/-! ## The packet as an `L²` class -/

/-- The `L²` class of the rational hard-edge packet with angular profile `cosPoly N b`. -/
def routeUCayleyPacket (a : ℝ) (ha : 0 < a) (N : ℕ) (b : ℕ → ℝ) : Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_routeUCayleyChain ha (realTrigDeg_cosPoly N b) 0).toLp
    (routeUCayleyChain a (cosPoly N b) 0)

theorem routeUCayleyPacket_highFrequency_le {a : ℝ} (ha : 0 < a) (N : ℕ) (b : ℕ → ℝ)
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    r ^ m * ‖restrictLp (highFrequencySet r) (𝓕 (routeUCayleyPacket a ha N b))‖
      ≤ (∏ i ∈ Finset.range m, (1 / a) * (1 / 2 + 2 * ((N : ℝ) + (i : ℝ))))
        * ‖routeUCayleyPacket a ha N b‖ :=
  routeUCayley_highFrequency_le ha (realTrigDeg_cosPoly N b) hr m

/-- The packet is the complexification of the rational hard-edge test. -/
theorem routeUCayleyPacket_eq_ofRealLp {a : ℝ} (ha : 0 < a) (p : Polynomial ℝ) {N : ℕ} {b : ℕ → ℝ}
    (hb : routeUHardEdgeAngularPoly a p
      = ∑ j ∈ Finset.range (N + 1),
        Polynomial.C (b j) * Polynomial.Chebyshev.T ℝ (j : ℤ)) :
    routeUCayleyPacket a ha N b
      = ofRealLp ((memLp_routeUHardEdgeRationalTest ha p).toLp
          (routeUHardEdgeRationalTest a p)) := by
  have hfun : routeUCayleyChain a (cosPoly N b) 0
      = fun x : ℝ => ((routeUHardEdgeRationalTest a p x : ℝ) : ℂ) := by
    funext x
    rw [routeUCayleyChain, trigCayleyIter_zero, ← routeUAngularDescendant_zero ha p hb,
      routeUAngularDescendant, cosPhasePoly_zero]
  rw [routeUCayleyPacket, ofRealLp_toLp]
  exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun x => congrFun hfun x)

/-! ## The Paley–Wiener support of a strong limit -/

/-- **(CSHC.20) The Fourier transform of a strong limit of normalized hard-edge packets of scaled
degree at most `C` vanishes above frequency `2C`.**  The limit therefore has exponential type at
most `2C`. -/
theorem routeUCayleyPacket_limit_highFrequency_eq_zero {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ} (ha : ∀ k : ℕ, 0 < a k)
    (haT : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ, ‖routeUCayleyPacket (a k) (ha k) (N k) (b k)‖ ≤ 1)
    {U : Lp ℂ 2 (volume : Measure ℝ)}
    (hU : Filter.Tendsto (fun k : ℕ => routeUCayleyPacket (a k) (ha k) (N k) (b k))
      Filter.atTop (nhds U))
    {δ : ℝ} (hδ : 0 < δ) :
    restrictLp (highFrequencySet (2 * C + δ)) (𝓕 U) = 0 := by
  have hr : (0 : ℝ) < 2 * C + δ := by linarith
  have key : ∀ m : ℕ, ‖restrictLp (highFrequencySet (2 * C + δ)) (𝓕 U)‖
      ≤ (2 * C) ^ m / (2 * C + δ) ^ m := by
    intro m
    refine norm_restrictLp_fourier_limit_le hU _
      (c := fun k : ℕ => (∏ i ∈ Finset.range m, (2 * C + (1 / 2 + 2 * (i : ℝ)) / a k))
        / (2 * C + δ) ^ m) ?_ ?_
    · intro k
      have hak : (0 : ℝ) < a k := ha k
      have hNk : ((N k : ℕ) : ℝ) ≤ C * a k := hNC k
      have hPnn : ∀ i : ℕ,
          (0 : ℝ) ≤ (1 / a k) * (1 / 2 + 2 * (((N k : ℕ) : ℝ) + (i : ℝ))) := by
        intro i
        have h1 : (0 : ℝ) ≤ ((N k : ℕ) : ℝ) := Nat.cast_nonneg _
        have h2 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        have h3 : (0 : ℝ) < 1 / a k := by positivity
        nlinarith
      have hbase := routeUCayleyPacket_highFrequency_le (ha k) (N k) (b k) hr m
      have hPle : (∏ i ∈ Finset.range m, (1 / a k) * (1 / 2 + 2 * (((N k : ℕ) : ℝ) + (i : ℝ))))
          ≤ ∏ i ∈ Finset.range m, (2 * C + (1 / 2 + 2 * (i : ℝ)) / a k) := by
        refine Finset.prod_le_prod (fun i _ => hPnn i) (fun i _ => ?_)
        have hexp : (1 / a k) * (1 / 2 + 2 * (((N k : ℕ) : ℝ) + (i : ℝ)))
            = (1 / 2 + 2 * ((N k : ℕ) : ℝ) + 2 * (i : ℝ)) / a k := by
          field_simp
          ring
        have hrhs : (2 * C * a k + (1 / 2 + 2 * (i : ℝ))) / a k
            = 2 * C + (1 / 2 + 2 * (i : ℝ)) / a k := by
          rw [add_div, mul_div_assoc, div_self (ne_of_gt hak), mul_one]
        rw [hexp, ← hrhs]
        exact (div_le_div_iff_of_pos_right hak).mpr (by linarith)
      have hchain : (2 * C + δ) ^ m
            * ‖restrictLp (highFrequencySet (2 * C + δ))
                (𝓕 (routeUCayleyPacket (a k) (ha k) (N k) (b k)))‖
          ≤ ∏ i ∈ Finset.range m, (2 * C + (1 / 2 + 2 * (i : ℝ)) / a k) := by
        refine le_trans hbase (le_trans ?_ hPle)
        refine le_trans (mul_le_mul_of_nonneg_left (hnorm k)
          (Finset.prod_nonneg fun i _ => hPnn i)) ?_
        rw [mul_one]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 * C + δ) ^ m)]
      calc ‖restrictLp (highFrequencySet (2 * C + δ))
              (𝓕 (routeUCayleyPacket (a k) (ha k) (N k) (b k)))‖ * (2 * C + δ) ^ m
          = (2 * C + δ) ^ m * ‖restrictLp (highFrequencySet (2 * C + δ))
              (𝓕 (routeUCayleyPacket (a k) (ha k) (N k) (b k)))‖ := by ring
        _ ≤ _ := hchain
    · have hfac : ∀ i ∈ Finset.range m,
          Filter.Tendsto (fun k : ℕ => 2 * C + (1 / 2 + 2 * (i : ℝ)) / a k)
            Filter.atTop (nhds (2 * C)) := by
        intro i _
        have h0 : Filter.Tendsto (fun k : ℕ => (1 / 2 + 2 * (i : ℝ)) / a k)
            Filter.atTop (nhds 0) := Filter.Tendsto.div_atTop tendsto_const_nhds haT
        have hconst : Filter.Tendsto (fun _ : ℕ => (2 * C : ℝ)) Filter.atTop (nhds (2 * C)) :=
          tendsto_const_nhds
        have hsum := hconst.add h0
        rwa [add_zero] at hsum
      have hprod := tendsto_finsetProd (Finset.range m) hfac
      rw [Finset.prod_const, Finset.card_range] at hprod
      exact hprod.div_const _
  have hzero : Filter.Tendsto (fun m : ℕ => (2 * C) ^ m / (2 * C + δ) ^ m)
      Filter.atTop (nhds 0) := by
    have heq : (fun m : ℕ => (2 * C) ^ m / (2 * C + δ) ^ m)
        = fun m : ℕ => ((2 * C) / (2 * C + δ)) ^ m := by
      funext m
      rw [div_pow]
    rw [heq]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
    rw [div_lt_one hr]
    linarith
  have hle : ‖restrictLp (highFrequencySet (2 * C + δ)) (𝓕 U)‖ ≤ 0 :=
    ge_of_tendsto' hzero key
  have : ‖restrictLp (highFrequencySet (2 * C + δ)) (𝓕 U)‖ = 0 :=
    le_antisymm hle (norm_nonneg _)
  exact norm_eq_zero.1 this


/-- **(CSHC.20) The Paley--Wiener support of a strong limit of normalized rational hard-edge
tests.**  Along a family of normalized nonpositive packets with `deg ≤ N k ≤ C·a k` and `a k → ∞`,
every strong `L²` limit has Fourier transform vanishing at every frequency with `2π|ξ| ≥ 2C + δ`. -/
theorem routeUHardEdge_limit_fourier_support {C : ℝ} (hC : 0 < C)
    {a : ℕ → ℝ} {p : ℕ → Polynomial ℝ} {N : ℕ → ℕ} {b : ℕ → ℕ → ℝ}
    (ha : ∀ k : ℕ, 0 < a k)
    (haT : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hb : ∀ k : ℕ, routeUHardEdgeAngularPoly (a k) (p k)
      = ∑ j ∈ Finset.range (N k + 1),
        Polynomial.C (b k j) * Polynomial.Chebyshev.T ℝ (j : ℤ))
    (hNC : ∀ k : ℕ, ((N k : ℕ) : ℝ) ≤ C * a k)
    (hnorm : ∀ k : ℕ, (∫ x : ℝ, routeUHardEdgeRationalTest (a k) (p k) x ^ 2) = 1)
    {L : Lp ℝ 2 (volume : Measure ℝ)}
    (hL : Filter.Tendsto (fun k : ℕ =>
      (memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))) Filter.atTop (nhds L))
    {δ : ℝ} (hδ : 0 < δ) :
    restrictLp (highFrequencySet (2 * C + δ)) (𝓕 (ofRealLp L)) = 0 := by
  have hpacket : ∀ k : ℕ, routeUCayleyPacket (a k) (ha k) (N k) (b k)
      = ofRealLp ((memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
          (routeUHardEdgeRationalTest (a k) (p k))) :=
    fun k => routeUCayleyPacket_eq_ofRealLp (ha k) (p k) (hb k)
  have hnorm' : ∀ k : ℕ, ‖routeUCayleyPacket (a k) (ha k) (N k) (b k)‖ ≤ 1 := by
    intro k
    have hsq : ‖(memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))‖ ^ 2 = 1 := by
      rw [norm_toLp_sq]
      exact hnorm k
    have h1 : ‖(memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k))‖ = 1 := by
      nlinarith [norm_nonneg ((memLp_routeUHardEdgeRationalTest (ha k) (p k)).toLp
        (routeUHardEdgeRationalTest (a k) (p k)))]
    rw [hpacket k, norm_ofRealLp, h1]
  have hU : Filter.Tendsto (fun k : ℕ => routeUCayleyPacket (a k) (ha k) (N k) (b k))
      Filter.atTop (nhds (ofRealLp L)) := by
    have hcont : Filter.Tendsto
        (fun v : Lp ℝ 2 (volume : Measure ℝ) => ofRealLp v) (nhds L) (nhds (ofRealLp L)) :=
      (Complex.ofRealCLM.compLpL 2 (volume : Measure ℝ)).continuous.tendsto L
    have hcomp := hcont.comp hL
    refine hcomp.congr fun k => ?_
    rw [hpacket k]
    rfl
  exact routeUCayleyPacket_limit_highFrequency_eq_zero hC ha haT hNC hnorm' hU hδ

end RHTower

end
