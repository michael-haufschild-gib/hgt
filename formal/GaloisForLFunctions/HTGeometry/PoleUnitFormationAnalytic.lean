import GaloisForLFunctions.HTGeometry.BallLogarithm
import GaloisForLFunctions.HTGeometry.PoleUnitFormationMechanics
import GaloisForLFunctions.HTGeometry.UpperEndPrimeLogJets

/-!
# Analytic layer of the pole-unit formation cocycle

A nonvanishing holomorphic unit on a disc has a distinguished logarithm vanishing at the centre,
and the regular-scale response is exactly the exponential of the increment of that logarithm.

Two statements are proved about how much of the unit a *single* relative scale sees.

* Coefficientwise: the correction ray `ε ↦ L (q ε) - L ε` has Taylor coefficients
  `(q ^ k - 1)` times those of `L`, so every nonresonant scale inverts the correction packet.
* Germwise: if two units have the same value at the centre and the same response at one scale of
  modulus `> 1`, their germs at the centre coincide; by the identity theorem they then agree on
  every connected domain carrying both, hence carry the same divisor.
-/

open Complex Metric Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The distinguished logarithm and the exact ghost law -/

/-- **Distinguished logarithm of a regular unit.**  A nonvanishing holomorphic function on a disc
centred at the origin is its value at the origin times `exp` of a holomorphic function vanishing
there. -/
theorem exists_unitLog {U : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hU : DifferentiableOn ℂ U (ball 0 R)) (hne : ∀ z ∈ ball (0 : ℂ) R, U z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (ball 0 R) ∧ L 0 = 0 ∧
      ∀ z ∈ ball (0 : ℂ) R, U z = U 0 * Complex.exp (L z) :=
  exists_log_on_ball hR hU hne

/-- **Exact ghost law.**  Through a distinguished logarithm the regular-unit response is the
exponential of the logarithmic increment between the two scales. -/
theorem correctedScaleResponse_eq_exp_sub {U L : ℂ → ℂ} {R : ℝ} {ε w : ℂ}
    (hlog : ∀ z ∈ ball (0 : ℂ) R, U z = U 0 * Complex.exp (L z))
    (hU0 : U 0 ≠ 0) (hε : ε ∈ ball (0 : ℂ) R) (hεw : ε * w ∈ ball (0 : ℂ) R) :
    correctedScaleResponse U ε w = Complex.exp (L (ε * w) - L ε) := by
  rw [correctedScaleResponse, hlog _ hε, hlog _ hεw, Complex.exp_sub]
  field_simp

/-! ## Scale action on the Taylor coefficients -/

/-- **Scale action on Taylor coefficients.**  Precomposing with multiplication by `q` multiplies
the `k`-th derivative by `q ^ k`, at every point whose image lies in the analyticity domain. -/
theorem iteratedDeriv_comp_const_mul_of_analyticOnNhd {V : Set ℂ} (hV : IsOpen V) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L V) (q : ℂ) :
    ∀ (k : ℕ) {z : ℂ}, q * z ∈ V →
      iteratedDeriv k (fun ε => L (q * ε)) z = q ^ k * iteratedDeriv k L (q * z) := by
  intro k
  induction k with
  | zero => intro z _; simp
  | succ k ih =>
      intro z hz
      have hWopen : IsOpen ((fun w : ℂ => q * w) ⁻¹' V) :=
        hV.preimage (by fun_prop)
      have hzW : z ∈ (fun w : ℂ => q * w) ⁻¹' V := hz
      have heq : iteratedDeriv k (fun ε => L (q * ε))
          =ᶠ[𝓝 z] fun w => q ^ k * iteratedDeriv k L (q * w) := by
        filter_upwards [hWopen.mem_nhds hzW] with w hw using ih hw
      have hg : DifferentiableAt ℂ (iteratedDeriv k L) (q * z) :=
        (analyticOnNhd_iteratedDeriv hL k _ hz).differentiableAt
      have hmul : HasDerivAt (fun w : ℂ => q * w) q z := by
        simpa using (hasDerivAt_id z).const_mul q
      have hcomp : HasDerivAt (fun w : ℂ => iteratedDeriv k L (q * w))
          (deriv (iteratedDeriv k L) (q * z) * q) z :=
        HasDerivAt.comp z hg.hasDerivAt hmul
      have hscaled : HasDerivAt (fun w : ℂ => q ^ k * iteratedDeriv k L (q * w))
          (q ^ k * (deriv (iteratedDeriv k L) (q * z) * q)) z := hcomp.const_mul _
      rw [iteratedDeriv_succ, heq.deriv_eq, hscaled.deriv, iteratedDeriv_succ]
      ring

/-! ## One-ray correction packet -/

/-- The logarithmic correction packet read along the single relative scale `q`. -/
def correctionRay (q : ℂ) (L : ℂ → ℂ) : ℂ → ℂ := fun ε => L (q * ε) - L ε

/-- **Correction-ray coefficient law.**  On one scale ray the `k`-th Taylor coefficient of the
correction packet is `q ^ k - 1` times the `k`-th coefficient of the logarithm. -/
theorem iteratedDeriv_correctionRay {V : Set ℂ} (hV : IsOpen V) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L V) (q : ℂ) (h0 : (0 : ℂ) ∈ V) (k : ℕ) :
    iteratedDeriv k (correctionRay q L) 0 = (q ^ k - 1) * iteratedDeriv k L 0 := by
  have hq0 : q * (0 : ℂ) ∈ V := by simpa using h0
  have hcomp : AnalyticAt ℂ (fun ε => L (q * ε)) 0 := by
    have hmul : AnalyticAt ℂ (fun ε : ℂ => q * ε) 0 :=
      (analyticAt_const).mul analyticAt_id
    have hcompose : AnalyticAt ℂ (L ∘ fun ε : ℂ => q * ε) 0 := (hL _ hq0).comp hmul
    simpa [Function.comp_def] using hcompose
  have hsub : iteratedDeriv k ((fun ε => L (q * ε)) - L) 0
      = iteratedDeriv k (fun ε => L (q * ε)) 0 - iteratedDeriv k L 0 :=
    iteratedDeriv_sub hcomp.contDiffAt (hL _ h0).contDiffAt
  have hray : correctionRay q L = (fun ε => L (q * ε)) - L := rfl
  rw [hray, hsub, iteratedDeriv_comp_const_mul_of_analyticOnNhd hV hL q k hq0]
  simp
  ring

/-- **One-ray reconstruction of the logarithm.**  Every scale which is nonresonant in degree `k`
recovers the `k`-th logarithmic coefficient from the correction packet. -/
theorem iteratedDeriv_of_correctionRay {V : Set ℂ} (hV : IsOpen V) {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L V) (q : ℂ) (h0 : (0 : ℂ) ∈ V) (k : ℕ) (hq : q ^ k - 1 ≠ 0) :
    iteratedDeriv k L 0 = iteratedDeriv k (correctionRay q L) 0 / (q ^ k - 1) := by
  rw [iteratedDeriv_correctionRay hV hL q h0 k]
  field_simp

/-! ## Germ rigidity from a single scale -/

/-- **One-ray germ rigidity.**  Two units with the same value at the origin and the same regular
response at a single scale of modulus greater than one have the same germ at the origin.  The
proof pulls the scale back: the response identity at `ε / q` makes the ratio `U / V` invariant
under division by `q`, and iterating drives the argument to the origin. -/
theorem eventuallyEq_of_oneRay {U V : ℂ → ℂ} {q : ℂ} (hq : 1 < ‖q‖)
    (hU : ContinuousAt U 0) (hV : ContinuousAt V 0) (hV0 : V 0 ≠ 0) (hUV0 : U 0 = V 0)
    (hneU : ∀ᶠ z in 𝓝 (0 : ℂ), U z ≠ 0) (hne : ∀ᶠ z in 𝓝 (0 : ℂ), V z ≠ 0)
    (hray : ∀ᶠ ε in 𝓝 (0 : ℂ), correctedScaleResponse U ε q = correctedScaleResponse V ε q) :
    ∀ᶠ z in 𝓝 (0 : ℂ), U z = V z := by
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at hq
    simp at hq
    linarith
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hneU.and (hne.and hray))
  -- the ratio of the two units
  set W : ℂ → ℂ := fun z => U z / V z with hW
  have hWcont : ContinuousAt W 0 := hU.div hV hV0
  have hW0 : W 0 = 1 := by
    rw [hW]
    simp [hUV0, div_self hV0]
  have hstep : ∀ z ∈ ball (0 : ℂ) δ, W z = W (z / q) := by
    intro z hz
    have hzq : z / q ∈ ball (0 : ℂ) δ := by
      simp only [mem_ball, dist_zero_right, norm_div] at hz ⊢
      calc ‖z‖ / ‖q‖ ≤ ‖z‖ := div_le_self (norm_nonneg z) hq.le
        _ < δ := hz
    obtain ⟨hUz1, hVz1, hrayz⟩ := hball _ hzq
    obtain ⟨hUz2, hVz2, _⟩ := hball _ hz
    have hcancel : z / q * q = z := div_mul_cancel₀ z hq0
    rw [correctedScaleResponse, correctedScaleResponse, hcancel] at hrayz
    rw [hW]
    field_simp at hrayz ⊢
    linear_combination hrayz
  have hiter : ∀ (n : ℕ), ∀ z ∈ ball (0 : ℂ) δ, W z = W (z / q ^ n) := by
    intro n
    induction n with
    | zero => intro z _; simp
    | succ n ih =>
        intro z hz
        have hmem : ∀ m : ℕ, z / q ^ m ∈ ball (0 : ℂ) δ := by
          intro m
          simp only [mem_ball, dist_zero_right, norm_div, norm_pow] at hz ⊢
          have h1 : (1 : ℝ) ≤ ‖q‖ ^ m := one_le_pow₀ (le_of_lt hq)
          calc ‖z‖ / ‖q‖ ^ m ≤ ‖z‖ := div_le_self (norm_nonneg z) h1
            _ < δ := hz
        rw [ih z hz, hstep _ (hmem n)]
        congr 1
        rw [div_div, pow_succ]
  have htend : ∀ z : ℂ, Tendsto (fun n : ℕ => z / q ^ n) atTop (𝓝 0) := by
    intro z
    have : Tendsto (fun n : ℕ => ‖z / q ^ n‖) atTop (𝓝 0) := by
      simp only [norm_div, norm_pow]
      have hgeom : Tendsto (fun n : ℕ => (‖q‖⁻¹) ^ n) atTop (𝓝 0) := by
        apply tendsto_pow_atTop_nhds_zero_of_lt_one
        · positivity
        · rw [inv_lt_one_iff₀]
          right; exact hq
      have := hgeom.const_mul ‖z‖
      simpa [div_eq_mul_inv, inv_pow] using this
    exact tendsto_zero_iff_norm_tendsto_zero.mpr this
  refine Metric.eventually_nhds_iff_ball.mpr ⟨δ, hδ, ?_⟩
  intro z hz
  have hconst : Tendsto (fun _ : ℕ => W z) atTop (𝓝 (W 0)) := by
    have hcomp : Tendsto (fun n : ℕ => W (z / q ^ n)) atTop (𝓝 (W 0)) :=
      hWcont.tendsto.comp (htend z)
    refine hcomp.congr ?_
    intro n
    exact (hiter n z hz).symm
  have hWz : W z = W 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  rw [hW0] at hWz
  obtain ⟨-, hVz, -⟩ := hball _ hz
  rw [hW] at hWz
  field_simp at hWz
  exact hWz

/-! ## Complete divisor memory -/

/-- **Complete formation memory.**  Equality of germs at the origin propagates through every
connected domain carrying both units. -/
theorem eqOn_of_eventuallyEq {U V : ℂ → ℂ} {Ω : Set ℂ} (hconn : IsPreconnected Ω)
    (hU : AnalyticOnNhd ℂ U Ω) (hV : AnalyticOnNhd ℂ V Ω) (h0 : (0 : ℂ) ∈ Ω)
    (hgerm : U =ᶠ[𝓝 0] V) : Set.EqOn U V Ω :=
  hU.eqOn_of_preconnected_of_eventuallyEq hV hconn h0 hgerm

/-- **Divisor memory of the one-ray correction tower.**  Two regular units with a common marked
value and a common response at one scale of modulus greater than one define meromorphic sources
with the same divisor on every connected continuation domain. -/
theorem divisorMemory_of_oneRay {U V : ℂ → ℂ} {Ω : Set ℂ} {q : ℂ} (r : ℕ) (hq : 1 < ‖q‖)
    (hconn : IsPreconnected Ω) (hU : AnalyticOnNhd ℂ U Ω) (hV : AnalyticOnNhd ℂ V Ω)
    (h0 : (0 : ℂ) ∈ Ω) (hV0 : V 0 ≠ 0) (hUV0 : U 0 = V 0)
    (hneU : ∀ᶠ z in 𝓝 (0 : ℂ), U z ≠ 0) (hne : ∀ᶠ z in 𝓝 (0 : ℂ), V z ≠ 0)
    (hray : ∀ᶠ ε in 𝓝 (0 : ℂ), correctedScaleResponse U ε q = correctedScaleResponse V ε q) :
    Set.EqOn U V Ω ∧
      ∀ z ∈ Ω, z ≠ 0 → ((z ^ r)⁻¹ * U z = 0 ↔ (z ^ r)⁻¹ * V z = 0) := by
  have hgerm : U =ᶠ[𝓝 (0 : ℂ)] V :=
    eventuallyEq_of_oneRay hq (hU _ h0).continuousAt (hV _ h0).continuousAt hV0 hUV0 hneU hne hray
  have heq : Set.EqOn U V Ω := eqOn_of_eventuallyEq hconn hU hV h0 hgerm
  refine ⟨heq, ?_⟩
  intro z hz _
  rw [heq hz]

end

end GaloisForLFunctions.HTGeometry
