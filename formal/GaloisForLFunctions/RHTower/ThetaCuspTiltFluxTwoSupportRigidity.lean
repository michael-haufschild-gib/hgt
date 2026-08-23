import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityEulerRayWeld

/-!
# Two-support rigidity for the literal theta-cusp tilt flux

The complete Xi squared-Euler response is strictly positive on every two distinct exterior
real nodes.  This module removes an artificial packet-size restriction: any finite exponential
packet whose nodes take only two such values collapses exactly to the corresponding two-mode
packet after coefficients are summed over equal-node fibres.

The resulting quadratic form is positive definite on the two aggregated coefficients.  Hence a
negative literal theta-cusp tilt-flux witness cannot be hidden in multiplicities or duplicate
nodes.  It must use a genuinely nonreal node or at least three distinct real Euler-ray nodes.

All results are unconditional.  The last theorem classifies the geometry of any counter-witness
under `not RiemannHypothesis`; it does not assert that such a witness exists unconditionally.

Claim labels: `[LEAN-PROVED] [BRIDGE/OBSTRUCTION] [NOVELTY UNVERIFIED]`.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Strict two-mode positivity -/

/-- The real-ray two-channel kernel is positive definite, not merely positive semidefinite, on
two distinct exterior nodes. -/
theorem twoMode_twoChannelKernel_realRay_energy_pos
    {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (c : Fin 2 → ℂ) (hc : c ≠ 0) :
    let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
      ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
        ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
    0 < (kernelEnergy twoChannelKernel c nodes).re := by
  dsimp only
  let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
    ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
      ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
  let A := xiSquaredEulerFullKernel x x
  let B := xiSquaredEulerFullKernel y y
  let C := xiSquaredEulerFullKernel x y
  have hy : 1 / 2 < y := hx.trans hxy
  have hA : 0 < A := xiSquaredEulerFullKernel_diag_pos (by linarith)
  have hdet : 0 < A * B - C ^ 2 := by
    exact xiSquaredEulerFullKernel_twoPoint_det_pos (by linarith) hxy
  have henergy :
      (kernelEnergy twoChannelKernel c nodes).re =
        A * Complex.normSq (c 0) + B * Complex.normSq (c 1) +
          2 * C * (conj (c 0) * c 1).re := by
    simp only [kernelEnergy, Fin.sum_univ_two, nodes, Matrix.cons_val_zero,
      Matrix.cons_val_one, twoChannelKernel_eq]
    rw [criticalLogDerivKernel_ofReal_eq_fullKernel hx hx,
      criticalLogDerivKernel_ofReal_eq_fullKernel hx hy,
      criticalLogDerivKernel_ofReal_eq_fullKernel hy hx,
      criticalLogDerivKernel_ofReal_eq_fullKernel hy hy]
    simp only [Complex.add_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, A, B, C]
    rw [show xiSquaredEulerFullKernel y x = xiSquaredEulerFullKernel x y by
      simp [xiSquaredEulerFullKernel, eulerRayResponseKernel, add_comm]]
    simp only [Complex.normSq_apply]
    ring
  have hsquares :
      0 < (A * (c 0).re + C * (c 1).re) ^ 2 +
          (A * (c 0).im + C * (c 1).im) ^ 2 +
          (A * B - C ^ 2) * ((c 1).re ^ 2 + (c 1).im ^ 2) := by
    by_cases h1 : c 1 = 0
    · have h0 : c 0 ≠ 0 := by
        intro h0
        apply hc
        funext j
        fin_cases j <;> assumption
      have hnorm0 : 0 < (c 0).re ^ 2 + (c 0).im ^ 2 := by
        simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_pos.mpr h0
      have hA2 : 0 < A ^ 2 := sq_pos_of_pos hA
      rw [h1]
      simp only [Complex.zero_re, Complex.zero_im, mul_zero, add_zero]
      nlinarith [mul_pos hA2 hnorm0]
    · have hnorm1 : 0 < (c 1).re ^ 2 + (c 1).im ^ 2 := by
        simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_pos.mpr h1
      have hlast :
          0 < (A * B - C ^ 2) * ((c 1).re ^ 2 + (c 1).im ^ 2) :=
        mul_pos hdet hnorm1
      nlinarith [sq_nonneg (A * (c 0).re + C * (c 1).re),
        sq_nonneg (A * (c 0).im + C * (c 1).im)]
  have hscaled :
      A * (A * Complex.normSq (c 0) + B * Complex.normSq (c 1) +
          2 * C * (conj (c 0) * c 1).re) =
        (A * (c 0).re + C * (c 1).re) ^ 2 +
          (A * (c 0).im + C * (c 1).im) ^ 2 +
          (A * B - C ^ 2) * ((c 1).re ^ 2 + (c 1).im ^ 2) := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re,
      Complex.conj_im]
    ring
  rw [henergy]
  have hprod :
      0 < A * (A * Complex.normSq (c 0) + B * Complex.normSq (c 1) +
        2 * C * (conj (c 0) * c 1).re) := by
    rw [hscaled]
    exact hsquares
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · exact (not_lt_of_ge hA.le hneg.1).elim

/-- Strict two-channel parity domination on two distinct exterior real nodes. -/
theorem twoMode_twoChannelParityEnergy_strict_domination_realRay
    {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (c : Fin 2 → ℂ) (hc : c ≠ 0) :
    let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
      ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
        ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
    xiWeilOddEnergy (channelPacketA c nodes) +
        xiWeilOddEnergy (channelPacketB c nodes) <
      xiWeilEvenEnergy (channelPacketA c nodes) +
        xiWeilEvenEnergy (channelPacketB c nodes) := by
  dsimp only
  let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
    ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
      ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
  have hconj : (fun j => conj (c j)) ≠ (0 : Fin 2 → ℂ) := by
    intro h
    apply hc
    funext j
    have hj := congrFun h j
    have := congrArg conj hj
    simpa using this
  have hpacket :
      0 < (xiWeilPolarization (channelPacketA c nodes) (channelPacketA c nodes) +
          xiWeilPolarization (channelPacketB c nodes) (channelPacketB c nodes)).re := by
    rw [twoChannel_packet_eq_kernelEnergy]
    exact twoMode_twoChannelKernel_realRay_energy_pos hx hxy (fun j => conj (c j)) hconj
  have hA := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiWeilSquareSummable_channelPacketA c nodes)
  have hB := xiWeilPolarization_self_eq_evenEnergy_sub_oddEnergy
    (xiWeilSquareSummable_channelPacketB c nodes)
  rw [hA, hB] at hpacket
  simp only [Complex.add_re, Complex.ofReal_re] at hpacket
  linarith

/-- A nonzero two-mode literal theta packet on distinct exterior real nodes has strictly positive
neutral tilt derivative. -/
theorem thetaCuspTiltSource_twoMode_realRay_tiltFlux_pos
    {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y) (c : Fin 2 → ℂ) (hc : c ≠ 0) {D : ℝ}
    (hD : HasDerivAt
      (tiltCorrelation thetaCuspTiltSource c ![(x : ℂ), (y : ℂ)]) D 0) :
    0 < D := by
  let a : ℝ := (1 / 2 + x) / 2
  have ha : 1 / 2 < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hay : a < y := hax.trans hxy
  let rawNodes : Fin 2 → ℂ := ![(x : ℂ), (y : ℂ)]
  let d : Fin 2 → ℂ := fun j => c j * xiCent (rawNodes j)
  let nodes : Fin 2 → {W : ℂ // 1 / 2 < W.re} :=
    ![⟨(x : ℂ), by norm_num at hx ⊢; exact hx⟩,
      ⟨(y : ℂ), by norm_num at hx ⊢; simp; linarith⟩]
  have hraw : ∀ j, 1 / 2 < (rawNodes j).re := by
    intro j
    fin_cases j
    · change 1 / 2 < ((x : ℂ)).re
      simpa only [Complex.ofReal_re] using hx
    · change 1 / 2 < ((y : ℂ)).re
      simpa only [Complex.ofReal_re] using hx.trans hxy
  have hd : d ≠ 0 := by
    intro hd0
    apply hc
    funext j
    have hj := congrFun hd0 j
    dsimp only [d] at hj
    exact (mul_eq_zero.mp hj).resolve_right
      (xiCent_ne_zero_of_half_lt_re (hraw j))
  have hEq :=
    tiltCorrelation_thetaCuspTiltSource_deriv_eq_twoChannelParityDeficit
      ha c rawNodes (fun j => by fin_cases j <;> simp [rawNodes, hax, hay]) hD
  dsimp only at hEq
  change D = xiWeilEvenEnergy (channelPacketA d nodes) +
      xiWeilEvenEnergy (channelPacketB d nodes) -
        (xiWeilOddEnergy (channelPacketA d nodes) +
          xiWeilOddEnergy (channelPacketB d nodes)) at hEq
  have hdom := twoMode_twoChannelParityEnergy_strict_domination_realRay hx hxy d hd
  dsimp only at hdom
  change xiWeilOddEnergy (channelPacketA d nodes) +
      xiWeilOddEnergy (channelPacketB d nodes) <
        xiWeilEvenEnergy (channelPacketA d nodes) +
          xiWeilEvenEnergy (channelPacketB d nodes) at hdom
  linarith

/-! ## Exact collapse of arbitrary finite two-support packets -/

/-- Sum of coefficients carried by one node. -/
def twoNodeAggregate {n : ℕ} (c w : Fin n → ℂ) (x : ℂ) : ℂ :=
  ∑ j with w j = x, c j

/-- The two aggregated coefficients of a packet. -/
def twoNodeCollapsedCoefficients {n : ℕ} (c w : Fin n → ℂ) (x y : ℂ) : Fin 2 → ℂ :=
  ![twoNodeAggregate c w x, twoNodeAggregate c w y]

/-- The collapsed two-node family. -/
def twoNodeCollapsedNodes (x y : ℂ) : Fin 2 → ℂ := ![x, y]

/-- A finite exponential packet supported on two nodes is exactly its fibre-aggregated two-mode
packet.  Duplicate nodes therefore carry no hidden quadratic information. -/
theorem expPacketFn_twoNodeCollapse {n : ℕ} (c w : Fin n → ℂ) (x y : ℂ)
    (hxy : x ≠ y) (hw : ∀ j, w j = x ∨ w j = y) (t : ℝ) :
    expPacketFn c w t =
      expPacketFn (twoNodeCollapsedCoefficients c w x y) (twoNodeCollapsedNodes x y) t := by
  classical
  simp only [expPacketFn, twoNodeCollapsedCoefficients, twoNodeCollapsedNodes,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, twoNodeAggregate]
  calc
    (∑ j, c j * Complex.exp (w j * (t : ℂ))) =
        (∑ j with w j = x, c j * Complex.exp (w j * (t : ℂ))) +
          ∑ j with w j ≠ x, c j * Complex.exp (w j * (t : ℂ)) := by
      exact (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j => w j = x) (fun j => c j * Complex.exp (w j * (t : ℂ)))).symm
    _ = (∑ j with w j = x, c j) * Complex.exp (x * (t : ℂ)) +
          (∑ j with w j ≠ x, c j) * Complex.exp (y * (t : ℂ)) := by
      congr 1
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j hj => by
          rw [(Finset.mem_filter.mp hj).2]
      · rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j hj => by
          have hjy := (hw j).resolve_left (Finset.mem_filter.mp hj).2
          rw [hjy]
    _ = (∑ j with w j = x, c j) * Complex.exp (x * (t : ℂ)) +
          (∑ j with w j = y, c j) * Complex.exp (y * (t : ℂ)) := by
      congr 2
      apply Finset.sum_congr
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hj
          exact (hw j).resolve_left hj
        · intro hjy hjx
          exact hxy (hjx.symm.trans hjy)
      · intro j hj
        rfl

/-- Two-support collapse commutes with the tilted source window. -/
theorem tiltWindow_twoNodeCollapse (S : ThetaSource) {n : ℕ}
    (c w : Fin n → ℂ) (x y : ℂ) (hxy : x ≠ y)
    (hw : ∀ j, w j = x ∨ w j = y) (a s : ℝ) :
    tiltWindow S c w a s =
      tiltWindow S (twoNodeCollapsedCoefficients c w x y) (twoNodeCollapsedNodes x y) a s := by
  rw [tiltWindow, tiltWindow]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  rw [expPacketFn_twoNodeCollapse c w x y hxy hw]

/-- Two-support collapse preserves the entire tilt-correlation function, not only its derivative
at the neutral tilt. -/
theorem tiltCorrelation_twoNodeCollapse (S : ThetaSource) {n : ℕ}
    (c w : Fin n → ℂ) (x y : ℂ) (hxy : x ≠ y)
    (hw : ∀ j, w j = x ∨ w j = y) (a : ℝ) :
    tiltCorrelation S c w a =
      tiltCorrelation S (twoNodeCollapsedCoefficients c w x y)
        (twoNodeCollapsedNodes x y) a := by
  rw [tiltCorrelation, tiltCorrelation]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [tiltWindow_twoNodeCollapse S c w x y hxy hw]

/-! ## Minimal geometry of a negative RH witness -/

/-- Every finite literal theta packet supported on at most two distinct exterior real nodes has
nonnegative neutral tilt flux, independently of packet size and multiplicity. -/
theorem thetaCuspTiltSource_twoSupport_realRay_tiltFlux_nonneg
    {n : ℕ} (c w : Fin n → ℂ) {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y)
    (hw : ∀ j, w j = (x : ℂ) ∨ w j = (y : ℂ)) {D : ℝ}
    (hD : HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0) :
    0 ≤ D := by
  let c₂ := twoNodeCollapsedCoefficients c w (x : ℂ) (y : ℂ)
  let w₂ := twoNodeCollapsedNodes (x : ℂ) (y : ℂ)
  have hxyC : (x : ℂ) ≠ (y : ℂ) := by exact_mod_cast hxy.ne
  have hfun : tiltCorrelation thetaCuspTiltSource c w =
      tiltCorrelation thetaCuspTiltSource c₂ w₂ := by
    funext a
    exact tiltCorrelation_twoNodeCollapse thetaCuspTiltSource c w
      (x : ℂ) (y : ℂ) hxyC hw a
  rw [hfun] at hD
  exact thetaCuspTiltSource_twoMode_realRay_tiltFlux_nonneg hx hxy c₂ hD

/-- Exact nullspace classification: a two-support packet has strictly positive neutral flux as
soon as either aggregated node coefficient is nonzero. -/
theorem thetaCuspTiltSource_twoSupport_realRay_tiltFlux_pos
    {n : ℕ} (c w : Fin n → ℂ) {x y : ℝ} (hx : 1 / 2 < x) (hxy : x < y)
    (hw : ∀ j, w j = (x : ℂ) ∨ w j = (y : ℂ))
    (hc : twoNodeCollapsedCoefficients c w (x : ℂ) (y : ℂ) ≠ 0) {D : ℝ}
    (hD : HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0) :
    0 < D := by
  let c₂ := twoNodeCollapsedCoefficients c w (x : ℂ) (y : ℂ)
  let w₂ := twoNodeCollapsedNodes (x : ℂ) (y : ℂ)
  have hxyC : (x : ℂ) ≠ (y : ℂ) := by exact_mod_cast hxy.ne
  have hfun : tiltCorrelation thetaCuspTiltSource c w =
      tiltCorrelation thetaCuspTiltSource c₂ w₂ := by
    funext a
    exact tiltCorrelation_twoNodeCollapse thetaCuspTiltSource c w
      (x : ℂ) (y : ℂ) hxyC hw a
  rw [hfun] at hD
  exact thetaCuspTiltSource_twoMode_realRay_tiltFlux_pos hx hxy c₂ hc hD

/-- A negative literal theta tilt-flux witness cannot be supported on two exterior real nodes. -/
theorem not_exists_twoSupport_realRay_of_thetaCuspTiltFlux_neg
    {n : ℕ} (c w : Fin n → ℂ) {D : ℝ}
    (hD : HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0) (hneg : D < 0) :
    ¬ ∃ x y : ℝ, 1 / 2 < x ∧ x < y ∧
      ∀ j, w j = (x : ℂ) ∨ w j = (y : ℂ) := by
  rintro ⟨x, y, hx, hxy, hw⟩
  have hnonneg := thetaCuspTiltSource_twoSupport_realRay_tiltFlux_nonneg
    c w hx hxy hw hD
  linarith

/-- Under failure of RH, the exact tilt-flux criterion supplies a negative witness whose node
geometry cannot collapse to two exterior real values.  Thus any counter-witness is genuinely
complex or has at least three distinct real support points. -/
theorem exists_negative_thetaCuspTiltFlux_not_twoSupport_realRay
    (hRH : ¬ RiemannHypothesis) :
    ∃ (n : ℕ) (c w : Fin n → ℂ) (D : ℝ),
      (∀ j, 1 / 2 < (w j).re) ∧
      HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0 ∧
      D < 0 ∧
      ¬ ∃ x y : ℝ, 1 / 2 < x ∧ x < y ∧
        ∀ j, w j = (x : ℂ) ∨ w j = (y : ℂ) := by
  have hnotAll :
      ¬ ∀ (n : ℕ) (c w : Fin n → ℂ), (∀ j, 1 / 2 < (w j).re) →
        ∀ D : ℝ, HasDerivAt (tiltCorrelation thetaCuspTiltSource c w) D 0 → 0 ≤ D := by
    intro hall
    exact hRH (riemannHypothesis_iff_thetaCuspTiltSource_tiltFlux_nonneg.mpr hall)
  push Not at hnotAll
  obtain ⟨n, c, w, hw, D, hD, hneg⟩ := hnotAll
  exact ⟨n, c, w, D, hw, hD, hneg,
    not_exists_twoSupport_realRay_of_thetaCuspTiltFlux_neg c w hD hneg⟩

end

end RHTower
