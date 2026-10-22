import Mathlib
import GaloisForLFunctions.RHTower.CCM.CCMBoundaryStripTransfer

/-!
# The source–norm–support forgetful tower

For the two-leg carrier with swap `τ`, twisted swap `T_δ`, and central scaling `L_c`, the
transport defect

`D = T_δ L_c − L_c τ`

is the single scalar `a = c(δ − 1)` placed in one matrix cell, and the two-column carrier
`Γ = [D | T_δ D]` satisfies the exact Gram identity `Γ Γ* = |a|² I`.  Consequently the support of
`Γ` is all or nothing, its Moore–Penrose inverse scales every vector by exactly `|a|⁻¹`, and
`det(Γ Γ*) = |a|⁴`.

Arithmetic orientation, positive Hilbert geometry, and exact support are therefore not independent
constraints: they are the successive forgetful shadows `a ↦ |a|² ↦ [a = 0]` of one framed scalar,
the first forgetting phase and the second forgetting magnitude.  A central scalar twist of all
block transports leaves every relative channel unchanged, so exact-category data alone cannot
select the untwisted frame.
-/

namespace HTGeometry.ConstraintRelativity

open Matrix Complex

/-! ## The two-leg carrier -/

/-- The swap involution. -/
def legSwap : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The twisted swap with parameter `δ`. -/
def legTwist (δ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; δ, 0]

/-- The central scaling by `c`. -/
def legScale (c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![c, 0; 0, c]

/-- The framed source scalar `a = c(δ − 1)`. -/
def sourceScalar (δ c : ℂ) : ℂ := c * (δ - 1)

/-- The transport defect `D = T_δ L_c − L_c τ`. -/
def transportDefect (δ c : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  legTwist δ * legScale c - legScale c * legSwap

/-- **The defect is one scalar in the lower-left cell.** -/
theorem transportDefect_eq (δ c : ℂ) :
    transportDefect δ c = !![0, 0; sourceScalar δ c, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transportDefect, legTwist, legScale, legSwap, sourceScalar]
  ring

/-- **The transported defect is the same scalar in the upper-left cell.** -/
theorem legTwist_mul_transportDefect (δ c : ℂ) :
    legTwist δ * transportDefect δ c = !![sourceScalar δ c, 0; 0, 0] := by
  rw [transportDefect_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [legTwist, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two-column carrier `Γ = [D | T_δ D] : ℂ² ⊕ ℂ² → ℂ²`. -/
def legCarrier (δ c : ℂ) : Matrix (Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.of fun i => Sum.elim (transportDefect δ c i) ((legTwist δ * transportDefect δ c) i)

@[simp]
theorem legCarrier_inl (δ c : ℂ) (i j : Fin 2) :
    legCarrier δ c i (Sum.inl j) = (!![0, 0; sourceScalar δ c, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  show transportDefect δ c i j = _
  rw [transportDefect_eq]

@[simp]
theorem legCarrier_inr (δ c : ℂ) (i j : Fin 2) :
    legCarrier δ c i (Sum.inr j) = (!![sourceScalar δ c, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℂ) i j := by
  show (legTwist δ * transportDefect δ c) i j = _
  rw [legTwist_mul_transportDefect]

/-- **Explicit action of the carrier.**  `Γ(x, y) = a (y₀ e₀ + x₀ e₁)`. -/
theorem legCarrier_mulVec (δ c : ℂ) (x y : Fin 2 → ℂ) :
    legCarrier δ c *ᵥ Sum.elim x y
      = ![sourceScalar δ c * y 0, sourceScalar δ c * x 0] := by
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two]

/-! ## The exact Gram identity -/

/-- **`Γ Γ* = |a|² I`.**  The two nonzero rows of the carrier are orthogonal of equal norm. -/
theorem legCarrier_mul_conjTranspose (δ c : ℂ) :
    legCarrier δ c * (legCarrier δ c)ᴴ = ((normSq (sourceScalar δ c) : ℝ) : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self] <;>
    ring

/-- **`det(Γ Γ*) = |a|⁴`.** -/
theorem det_legCarrier_mul_conjTranspose (δ c : ℂ) :
    (legCarrier δ c * (legCarrier δ c)ᴴ).det = ((normSq (sourceScalar δ c) : ℝ) : ℂ) ^ 2 := by
  rw [legCarrier_mul_conjTranspose, Matrix.det_smul, Matrix.det_one, mul_one]
  simp

/-! ## Support: all or nothing -/

/-- If the framed scalar vanishes the carrier vanishes. -/
theorem legCarrier_eq_zero (δ c : ℂ) (ha : sourceScalar δ c = 0) : legCarrier δ c = 0 := by
  ext i j
  rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp [ha]

/-- If the framed scalar is nonzero the carrier is surjective. -/
theorem legCarrier_surjective (δ c : ℂ) (ha : sourceScalar δ c ≠ 0) (v : Fin 2 → ℂ) :
    ∃ w : Fin 2 ⊕ Fin 2 → ℂ, legCarrier δ c *ᵥ w = v := by
  refine ⟨Sum.elim ![v 1 / sourceScalar δ c, 0] ![v 0 / sourceScalar δ c, 0], ?_⟩
  rw [legCarrier_mulVec]
  ext i
  fin_cases i <;> simp [mul_div_cancel₀ _ ha]

/-! ## The Moore–Penrose inverse and its exact scaling -/

/-- The Moore–Penrose inverse of the carrier when the framed scalar is nonzero. -/
noncomputable def legCarrierPseudoInverse (δ c : ℂ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2) ℂ :=
  ((normSq (sourceScalar δ c) : ℝ) : ℂ)⁻¹ • (legCarrier δ c)ᴴ

/-- The pseudo-inverse is a right inverse. -/
theorem legCarrier_mul_pseudoInverse (δ c : ℂ) (ha : sourceScalar δ c ≠ 0) :
    legCarrier δ c * legCarrierPseudoInverse δ c = 1 := by
  have hns : ((normSq (sourceScalar δ c) : ℝ) : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero, Complex.normSq_eq_zero] using ha
  rw [legCarrierPseudoInverse, Matrix.mul_smul, legCarrier_mul_conjTranspose, smul_smul,
    inv_mul_cancel₀ hns, one_smul]

/-- **The adjoint carrier scales every vector by exactly `|a|`.** -/
theorem sum_normSq_conjTranspose_mulVec (δ c : ℂ) (x : Fin 2 → ℂ) :
    ∑ i, normSq (((legCarrier δ c)ᴴ *ᵥ x) i)
      = normSq (sourceScalar δ c) * ∑ i, normSq (x i) := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two,
    Matrix.conjTranspose_apply, Complex.normSq_mul, Complex.normSq_conj]
  ring

/-- **`‖Γ†x‖ = ‖x‖ / |a|`.**  The Moore–Penrose inverse scales every vector by exactly `|a|⁻¹`,
so its operator norm is `|a|⁻¹`. -/
theorem sum_normSq_pseudoInverse_mulVec (δ c : ℂ) (ha : sourceScalar δ c ≠ 0)
    (x : Fin 2 → ℂ) :
    ∑ i, normSq ((legCarrierPseudoInverse δ c *ᵥ x) i)
      = (∑ i, normSq (x i)) / normSq (sourceScalar δ c) := by
  have hns : normSq (sourceScalar δ c) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using ha
  have hsmul : ∀ i, (legCarrierPseudoInverse δ c *ᵥ x) i
      = ((normSq (sourceScalar δ c) : ℝ) : ℂ)⁻¹ * (((legCarrier δ c)ᴴ *ᵥ x) i) := by
    intro i
    simp only [legCarrierPseudoInverse, Matrix.mulVec, dotProduct, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
  calc ∑ i, normSq ((legCarrierPseudoInverse δ c *ᵥ x) i)
      = ∑ i, (normSq (sourceScalar δ c))⁻¹ ^ 2 * normSq (((legCarrier δ c)ᴴ *ᵥ x) i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsmul i, Complex.normSq_mul]
        simp [sq]
    _ = (normSq (sourceScalar δ c))⁻¹ ^ 2 * ∑ i, normSq (((legCarrier δ c)ᴴ *ᵥ x) i) := by
        rw [Finset.mul_sum]
    _ = (∑ i, normSq (x i)) / normSq (sourceScalar δ c) := by
        rw [sum_normSq_conjTranspose_mulVec]
        field_simp

/-! ## The three shadows -/

/-- The magnitude shadow forgets the phase: every nonzero framed scalar has a distinct companion
of the same magnitude. -/
theorem normSq_forgets_phase (a : ℂ) (ha : a ≠ 0) :
    ∃ b : ℂ, b ≠ a ∧ normSq b = normSq a := by
  refine ⟨-a, fun h => ha ?_, by simp⟩
  linear_combination (-1 / 2 : ℂ) * h

/-- The support shadow forgets the magnitude: two framed scalars can have the same vanishing
behaviour and different magnitudes. -/
theorem support_forgets_magnitude :
    ∃ a b : ℂ, ((a = 0) ↔ (b = 0)) ∧ normSq a ≠ normSq b :=
  ⟨1, 2, by norm_num, by norm_num [Complex.normSq_apply]⟩

/-- The support shadow factors through the magnitude shadow, which factors through the framed
scalar: the three route outputs are successive functions of one datum. -/
theorem shadow_tower (a : ℂ) : (a = 0) ↔ (normSq a = 0) := by
  simp

/-- **Card `(13)`, the three-shadow theorem.**  The three route outputs are not independent
constraints: the support shadow factors through the magnitude shadow, which factors through the
framed scalar, and each step forgets exactly what the card says — the magnitude forgets the phase
and coorientation, the support forgets the magnitude.  Because every component is already a
function of `a`, taking their product cannot create selection. -/
theorem three_shadow_theorem :
    (∀ a : ℂ, (a = 0) ↔ (normSq a = 0))
      ∧ (∀ a : ℂ, a ≠ 0 → ∃ b : ℂ, b ≠ a ∧ normSq b = normSq a)
      ∧ (∃ a b : ℂ, ((a = 0) ↔ (b = 0)) ∧ normSq a ≠ normSq b) :=
  ⟨shadow_tower, normSq_forgets_phase, support_forgets_magnitude⟩

/-! ## Central-twist isotriviality -/

/-- **Relative channels are blind to a central twist.**  Scaling every block transport by the same
nonzero scalar leaves every relative channel `T_j f T_i⁻¹` unchanged. -/
theorem relative_channel_central_twist {n : ℕ} (δ : ℂ) (hδ : δ ≠ 0)
    (Ti Tj f : Matrix (Fin n) (Fin n) ℂ) (hTi : IsUnit Ti.det) :
    (δ • Tj) * f * (δ • Ti)⁻¹ = Tj * f * Ti⁻¹ := by
  letI : Invertible δ := invertibleOfNonzero hδ
  rw [Matrix.inv_smul Ti δ hTi, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    invOf_mul_self, one_smul]

/-- A central twist does change the determinant holonomy, so the twist is visible to framed
determinant data even though it is invisible to relative channels. -/
theorem det_central_twist {n : ℕ} (δ : ℂ) (T : Matrix (Fin n) (Fin n) ℂ) :
    (δ • T).det = δ ^ n * T.det := by
  simp

/-! ## The arithmetic instantiation at the critical wall -/

section Wall

open Filter Topology

/-- **Card `(11)`.**  The wall parameter of a divisor copy at prime-cycle level `n`. -/
noncomputable def wallParameter (n : ℕ) (ρ : ℂ) : ℝ := (2 * ρ.re - 1) * Real.log n

/-- **Card `(9)`.**  The prime-cycle transport factor `δ_n(ρ) = e^{(2 Re ρ − 1) log n}`. -/
noncomputable def cycleTransport (n : ℕ) (ρ : ℂ) : ℂ :=
  ((Real.exp (wallParameter n ρ) : ℝ) : ℂ)

/-- **Card `(11)`.**  The wall parameter vanishes exactly on the critical line, once the cycle
level is at least two. -/
theorem wallParameter_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) (ρ : ℂ) :
    wallParameter n ρ = 0 ↔ ρ.re = 1 / 2 := by
  have hlog : Real.log n ≠ 0 := by
    have h1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn.trans_lt' one_lt_two
    exact ne_of_gt (Real.log_pos h1)
  rw [wallParameter, mul_eq_zero]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hlog
  · intro h
    left
    rw [h]
    ring

/-- **Card `(19)`.**  The framed residue of a divisor copy vanishes exactly on the critical line:
`Res(D_{n,ρ}u_p) = (δ_n(ρ) − 1) c_ρ` is zero iff the wall parameter is zero. -/
theorem sourceScalar_cycleTransport_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) (ρ c : ℂ) (hc : c ≠ 0) :
    sourceScalar (cycleTransport n ρ) c = 0 ↔ ρ.re = 1 / 2 := by
  rw [sourceScalar, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h hc
    · refine (wallParameter_eq_zero_iff hn ρ).1 ?_
      have h2 : ((Real.exp (wallParameter n ρ) : ℝ) : ℂ) = (1 : ℂ) := h
      have h' : Real.exp (wallParameter n ρ) = 1 := by exact_mod_cast h2
      exact (Real.exp_eq_one_iff _).1 h'
  · intro h
    right
    have hκ : wallParameter n ρ = 0 := (wallParameter_eq_zero_iff hn ρ).2 h
    rw [cycleTransport, hκ, Real.exp_zero, Complex.ofReal_one]

/-- **Card `(19)`, carrier form.**  The two-column carrier of a divisor copy degenerates to zero
exactly on the critical line. -/
theorem legCarrier_cycleTransport_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) (ρ c : ℂ) (hc : c ≠ 0) :
    legCarrier (cycleTransport n ρ) c = 0 ↔ ρ.re = 1 / 2 := by
  rw [← sourceScalar_cycleTransport_eq_zero_iff hn ρ c hc]
  constructor
  · intro h
    have hentry := congrFun (congrFun h 1) (Sum.inl 0)
    rw [legCarrier_inl] at hentry
    simpa using hentry
  · exact legCarrier_eq_zero _ _

/-- **Card `(19)`, conditioning form.**  Off the critical line the carrier of a divisor copy is
surjective; on it the carrier is zero.  The critical line is exactly the degeneration locus. -/
theorem legCarrier_cycleTransport_surjective {n : ℕ} (hn : 2 ≤ n) (ρ c : ℂ) (hc : c ≠ 0)
    (hρ : ρ.re ≠ 1 / 2) (v : Fin 2 → ℂ) :
    ∃ x : Fin 2 ⊕ Fin 2 → ℂ, legCarrier (cycleTransport n ρ) c *ᵥ x = v :=
  legCarrier_surjective _ _ (fun h => hρ ((sourceScalar_cycleTransport_eq_zero_iff hn ρ c hc).1 h)) v

/-- **Card `(9)`, `(10)`.**  The framed scalar of a divisor copy has squared magnitude
`|c|² (e^κ − 1)²`, where `κ` is the wall parameter. -/
theorem normSq_sourceScalar_cycleTransport (n : ℕ) (ρ c : ℂ) :
    normSq (sourceScalar (cycleTransport n ρ) c)
      = normSq c * (Real.exp (wallParameter n ρ) - 1) ^ 2 := by
  have hsub : cycleTransport n ρ - 1 = ((Real.exp (wallParameter n ρ) - 1 : ℝ) : ℂ) := by
    rw [cycleTransport, Complex.ofReal_sub, Complex.ofReal_one]
  rw [sourceScalar, map_mul, hsub, Complex.normSq_ofReal]
  ring

/-- **Card `(10)`.**  The carrier of a divisor copy has Gram matrix `|a_ρ|² I`. -/
theorem legCarrier_mul_conjTranspose_wall (n : ℕ) (ρ c : ℂ) :
    legCarrier (cycleTransport n ρ) c * (legCarrier (cycleTransport n ρ) c)ᴴ
      = ((normSq c * (Real.exp (wallParameter n ρ) - 1) ^ 2 : ℝ) : ℂ) • 1 := by
  rw [legCarrier_mul_conjTranspose, normSq_sourceScalar_cycleTransport]

/-- **Card `(12)`, exact form.**  The squared pseudo-inverse gain at a divisor copy is
`1 / (|c|² (e^κ − 1)²)`. -/
theorem sum_normSq_pseudoInverse_wall (n : ℕ) (ρ c : ℂ)
    (ha : sourceScalar (cycleTransport n ρ) c ≠ 0) (x : Fin 2 → ℂ) :
    ∑ i, normSq ((legCarrierPseudoInverse (cycleTransport n ρ) c *ᵥ x) i)
      = (∑ i, normSq (x i)) / (normSq c * (Real.exp (wallParameter n ρ) - 1) ^ 2) := by
  rw [sum_normSq_pseudoInverse_mulVec _ _ ha, normSq_sourceScalar_cycleTransport]

/-- **Card `(12)`.**  Near the critical wall the squared pseudo-inverse gain is asymptotically
`1/(|c|² κ²)`: the ratio of the exact gain to that model tends to one as the wall parameter tends
to zero.  This is the card's `‖Γ_ρ†‖ ∼ 1/(|c_ρ| |κ|)`, squared. -/
theorem tendsto_pseudoInverse_gain_ratio (c : ℂ) (hc : c ≠ 0) :
    Tendsto (fun κ : ℝ =>
        (normSq c * (Real.exp κ - 1) ^ 2)⁻¹ / (normSq c * κ ^ 2)⁻¹) (𝓝[≠] 0) (𝓝 1) := by
  have hns : normSq c ≠ 0 := by simpa [Complex.normSq_eq_zero] using hc
  have hneg : Tendsto (fun κ : ℝ => -κ) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with κ hκ
      exact neg_ne_zero.2 hκ
  have hbase : Tendsto (fun κ : ℝ => (Real.exp κ - 1) / κ) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    refine (GaloisForLFunctions.RHTower.tendsto_one_sub_exp_neg_div.comp hneg).congr fun κ => ?_
    show (1 - Real.exp (-(-κ))) / (-κ) = (Real.exp κ - 1) / κ
    rw [neg_neg, div_neg, neg_div', neg_sub]
  have hsq : Tendsto (fun κ : ℝ => ((Real.exp κ - 1) / κ) ^ 2) (𝓝[≠] 0) (𝓝 1) := by
    simpa using hbase.pow 2
  have hinv : Tendsto (fun κ : ℝ => (((Real.exp κ - 1) / κ) ^ 2)⁻¹) (𝓝[≠] 0) (𝓝 1) := by
    simpa using hsq.inv₀ one_ne_zero
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with κ hκ
  have hκ0 : κ ≠ 0 := hκ
  field_simp

/-- **Card `(12)`.**  The exact wall is a singular-conditioning wall: the squared pseudo-inverse
gain blows up as the wall parameter tends to zero. -/
theorem tendsto_pseudoInverse_gain_atTop (c : ℂ) (hc : c ≠ 0) :
    Tendsto (fun κ : ℝ => (normSq c * (Real.exp κ - 1) ^ 2)⁻¹) (𝓝[≠] 0) atTop := by
  have hns : 0 < normSq c := by
    simpa [Complex.normSq_pos] using hc
  refine Filter.Tendsto.inv_tendsto_nhdsGT_zero ?_
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcont : ContinuousAt (fun κ : ℝ => normSq c * (Real.exp κ - 1) ^ 2) 0 := by fun_prop
    have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
    simpa using h
  · filter_upwards [self_mem_nhdsWithin] with κ hκ
    have hκ0 : κ ≠ 0 := hκ
    have hexp : Real.exp κ - 1 ≠ 0 := by
      intro h
      exact hκ0 ((Real.exp_eq_one_iff κ).1 (by linarith))
    exact Set.mem_Ioi.2 (by positivity)

end Wall

end HTGeometry.ConstraintRelativity
