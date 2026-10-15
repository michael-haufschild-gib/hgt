import GaloisForLFunctions.RHTower.ThetaParityReferencePackets
import GaloisForLFunctions.RHTower.ApproximationNumberLowerBound
import GaloisForLFunctions.HTGeometry.EventualNegDefFromEntrywise

/-!
# Divergence of every fixed theta reference approximation number

For the actual finite reference operators A_(N+1) on unweighted source L2,
every fixed approximation number tends to infinity as N tends to infinity.
The theorem has no theta zero-location or spectral premise.

The proof uses the exact three-interval packet matrix limit. Finite quadratic-form
stability gives a positive lower bound on the coefficient space. The same bound
proves the input synthesis injective; elementary packet norm bounds then give
uniform expansion on its range. The approximation-number dimension lemma applies.
Choosing arbitrarily long source packets makes the lower bound arbitrarily large.

This proves the analytic divergence dependency of the directed-feedback obstruction.
Its comparison with the finite positive square core and the exterior residue signs
is separate; neither a critical-wall selection theorem nor RH is asserted here.
-/

open MeasureTheory Set Filter Topology Matrix
open scoped BigOperators InnerProductSpace
namespace RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

private def packetSynthesis {E : Type*} [AddCommGroup E] [Module ℂ E]
    {k : ℕ} (u : Fin k → E) : (Fin k → ℂ) →ₗ[ℂ] E where
  toFun x := ∑ i, x i • u i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul]

private theorem norm_packetSynthesis_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {k : ℕ} (u : Fin k → E) {C : ℝ} (hC : ∀ i, ‖u i‖ ≤ C) (x : Fin k → ℂ) :
    ‖packetSynthesis u x‖ ≤ (k : ℝ) * C * ‖x‖ := by
  calc
    ‖packetSynthesis u x‖ ≤ ∑ i, ‖x i‖ * ‖u i‖ := by
      simpa only [packetSynthesis, LinearMap.coe_mk, AddHom.coe_mk, norm_smul] using
        norm_sum_le (s := Finset.univ) (f := fun i => x i • u i)
    _ ≤ ∑ _i : Fin k, ‖x‖ * C := Finset.sum_le_sum fun i _ =>
      mul_le_mul (norm_le_pi_norm x i) (hC i) (norm_nonneg _) (norm_nonneg _)
    _ = (k : ℝ) * C * ‖x‖ := by simp; ring

private theorem inner_packetSynthesis {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {k : ℕ} (u v : Fin k → E) (T : E →L[ℂ] E) (x : Fin k → ℂ) :
    inner ℂ (packetSynthesis v x) (T (packetSynthesis u x)) =
      star x ⬝ᵥ Matrix.mulVec (fun i j => inner ℂ (v i) (T (u j))) x := by
  simp [packetSynthesis, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_assoc, mul_comm]
  rw [Finset.sum_comm]

private theorem eventually_packet_form {l : ℝ} (hl : 0 < l) (k : ℕ) :
    ∀ᶠ N in atTop, ∀ x : Fin k → ℂ,
      (Real.pi * l ^ 2 / 4) * ‖x‖ ^ 2 ≤
        (inner ℂ (packetSynthesis (fun i : Fin k => thetaParityOutputPacket l i) x)
          (thetaParityReferenceOperator (N + 1)
            (packetSynthesis (fun i : Fin k => thetaParityInputPacket l i) x))).re := by
  let G : ℕ → Matrix (Fin k) (Fin k) ℂ := fun N i j =>
    inner ℂ (thetaParityOutputPacket l i)
      (thetaParityReferenceOperator (N + 1) (thetaParityInputPacket l j))
  let c : ℝ := Real.pi / 2 * l ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hconv : ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ i j,
      ‖G N i j - (Matrix.diagonal fun _ : Fin k => (c : ℂ)) i j‖ ≤ ε := by
    intro ε hε
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    have ht : Tendsto (fun N => G N i j) atTop
        (𝓝 ((Matrix.diagonal fun _ : Fin k => (c : ℂ)) i j)) := by
      simpa only [G, c, Matrix.diagonal_apply, Fin.ext_iff, eq_comm] using
        tendsto_thetaParityPacket_matrix hl j i
    filter_upwards [ht.eventually (Metric.ball_mem_nhds _ hε)] with N hN
    exact (show ‖G N i j - (Matrix.diagonal fun _ : Fin k => (c : ℂ)) i j‖ < ε by
      simpa only [Metric.mem_ball, dist_eq_norm] using hN).le
  filter_upwards [eventually_quadForm_sub_diagonal_le G (fun _ => c) hc hconv] with N hN
  intro x
  have he := hN x
  rw [re_quadForm_diagonal, ← Finset.mul_sum] at he
  have hd := mul_le_mul_of_nonneg_left (sq_pi_norm_le_sum_sq x) hc.le
  have hlo := (abs_le.mp he).1
  rw [inner_packetSynthesis]
  change (Real.pi * l ^ 2 / 4) * ‖x‖ ^ 2 ≤ (star x ⬝ᵥ (G N).mulVec x).re
  dsimp [c] at hlo hd
  linarith

private theorem expansion_of_packet_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {k : ℕ} (U V : (Fin k → ℂ) →ₗ[ℂ] E) (T : E →L[ℂ] E)
    {C D δ r : ℝ} (hD : 0 < D) (hr : 0 ≤ r) (hδ : δ = r * C * D)
    (hU : ∀ x, ‖U x‖ ≤ C * ‖x‖) (hV : ∀ x, ‖V x‖ ≤ D * ‖x‖)
    (hform : ∀ x, δ * ‖x‖ ^ 2 ≤ (inner ℂ (V x) (T (U x))).re) (x : Fin k → ℂ) :
    r * ‖U x‖ ≤ ‖T (U x)‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hp : δ * ‖x‖ ^ 2 ≤ D * ‖x‖ * ‖T (U x)‖ := calc
    δ * ‖x‖ ^ 2 ≤ (inner ℂ (V x) (T (U x))).re := hform x
    _ ≤ ‖inner ℂ (V x) (T (U x))‖ := Complex.re_le_norm _
    _ ≤ ‖V x‖ * ‖T (U x)‖ := norm_inner_le_norm _ _
    _ ≤ D * ‖x‖ * ‖T (U x)‖ := mul_le_mul_of_nonneg_right (hV x) (norm_nonneg _)
  have hp' : δ * ‖x‖ ≤ D * ‖T (U x)‖ := by
    exact le_of_mul_le_mul_right
      (show (δ * ‖x‖) * ‖x‖ ≤ (D * ‖T (U x)‖) * ‖x‖ by nlinarith [hp]) hn
  have htarget : (r * ‖U x‖) * D ≤ ‖T (U x)‖ * D := by
    calc
      (r * ‖U x‖) * D ≤ (r * (C * ‖x‖)) * D := by gcongr; exact hU x
      _ = δ * ‖x‖ := by rw [hδ]; ring
      _ ≤ D * ‖T (U x)‖ := hp'
      _ = ‖T (U x)‖ * D := mul_comm _ _
  exact le_of_mul_le_mul_right htarget hD

/-- Every fixed-dimensional packet space is eventually expanded without bound as
its source intervals grow. Constants are deliberately rough. -/
theorem eventually_thetaParityReference_approxNumber_lower {l : ℝ} (hl : 0 < l) (n : ℕ) :
    ∀ᶠ N in atTop, Real.pi * l / (8 * (n + 1 : ℝ) ^ 2) ≤
      approxNumber (thetaParityReferenceOperator (N + 1)) n := by
  let k := n + 1
  let U := packetSynthesis (fun i : Fin k => thetaParityInputPacket l i)
  let V := packetSynthesis (fun i : Fin k => thetaParityOutputPacket l i)
  let C : ℝ := 2 * k * Real.sqrt l
  let D : ℝ := k * Real.sqrt l
  let δ : ℝ := Real.pi * l ^ 2 / 4
  let r : ℝ := Real.pi * l / (8 * (k : ℝ) ^ 2)
  have hk : (0 : ℝ) < k := by dsimp [k]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ = r * C * D := by
    dsimp [δ, r, C, D]
    have hs := Real.sq_sqrt hl.le
    field_simp
    nlinarith [hs]
  have hU : ∀ x, ‖U x‖ ≤ C * ‖x‖ := by
    intro x
    have h := norm_packetSynthesis_le (fun i : Fin k => thetaParityInputPacket l i)
      (fun i => norm_thetaParityInputPacket_le hl i) x
    dsimp [U, C]
    nlinarith [h]
  have hV : ∀ x, ‖V x‖ ≤ D * ‖x‖ := by
    intro x
    exact norm_packetSynthesis_le (fun i : Fin k => thetaParityOutputPacket l i)
      (fun i => (norm_thetaParityOutputPacket hl i).le) x
  filter_upwards [eventually_packet_form hl k] with N hN
  have hform : ∀ x, δ * ‖x‖ ^ 2 ≤
      (inner ℂ (V x) (thetaParityReferenceOperator (N + 1) (U x))).re := hN
  have hinj : Function.Injective U := by
    have hz : ∀ x, U x = 0 → x = 0 := by
      intro x hx
      have h := hform x
      rw [hx, map_zero, inner_zero_right, Complex.zero_re] at h
      have hsq : ‖x‖ ^ 2 ≤ 0 := by nlinarith
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
    intro x y hxy
    exact sub_eq_zero.mp (hz (x - y) (by rw [map_sub, hxy, sub_self]))
  have hdim : n + 1 ≤ Module.finrank ℂ (LinearMap.range U) := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have he : ∀ w ∈ LinearMap.range U, r * ‖w‖ ≤
      ‖thetaParityReferenceOperator (N + 1) w‖ := by
    rintro w ⟨x, rfl⟩
    exact expansion_of_packet_form U V _ hD hr hδr hU hV hform x
  have hh := le_approxNumber_of_subspace (LinearMap.range U) hdim he
  simpa only [r, k, Nat.cast_add, Nat.cast_one] using hh

/-- Every fixed approximation number of the actual positive-reference source
operator tends to infinity. No theta zero-location or spectral premise is used. -/
theorem tendsto_thetaParityReference_approxNumber_atTop (n : ℕ) :
    Tendsto (fun N => approxNumber (thetaParityReferenceOperator (N + 1)) n) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  let l : ℝ := 8 * (n + 1 : ℝ) ^ 2 * (max b 0 + 1) / Real.pi
  have hl : 0 < l := by dsimp [l]; positivity
  have he : Real.pi * l / (8 * (n + 1 : ℝ) ^ 2) = max b 0 + 1 := by
    dsimp [l]
    have hn : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
  filter_upwards [eventually_thetaParityReference_approxNumber_lower hl n] with N hN
  rw [he] at hN
  exact (by linarith [le_max_left b 0] : b ≤ max b 0 + 1).trans hN

end
end RHTower
