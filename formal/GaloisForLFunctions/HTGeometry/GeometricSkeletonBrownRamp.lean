import GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman

/-!
# A geometric endpoint skeleton forces a continuous lower ramp

Circuit composition transfers hardness backwards in time: preparing the state at time `t` and then
uniformly simulating the remaining evolution prepares the state at any later time.  If the
simulator costs at most `v u + A` for elapsed time `u`, hardness at a geometric skeleton of times
therefore forces a pointwise linear lower bound at *every* time of the interval, with the slope
reduced only by the geometric ratio.

Composition also gives the matching upper ramp from an easy seed, and the skeleton of a geometric
progression has only logarithmically many endpoints, so a reporter with an exponentially decaying
failure tail survives their union at logarithmic replica order.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

variable {X : Type*} [MetricSpace X] {Γ : Type*}

/-! ## Uniform simulation complexity -/

/-- Least word length of a gate circuit simulating the flow at elapsed time `u` uniformly on the
whole space to accuracy `gamma`. -/
def uniformSimComplexity (act : Γ → X → X) (U : ℝ → X → X) (gamma u : ℝ) : ℕ :=
  sInf {s : ℕ | ∃ w : List Γ, w.length ≤ s ∧ ∀ x, dist (wordAct act w x) (U u x) ≤ gamma}

omit [MetricSpace X] in
theorem wordAct_append (act : Γ → X → X) (w₁ w₂ : List Γ) (x : X) :
    wordAct act (w₁ ++ w₂) x = wordAct act w₁ (wordAct act w₂ x) := by
  simp [wordAct, List.foldr_append]

/-! ## Backward composition -/

/-- **Composition transfer.**  Preparing the time-`t` state and then simulating the remaining
elapsed time `u` prepares the time-`u + t` state, with the errors and the word lengths adding. -/
theorem approxComplexity_le_add_of_witnesses
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    (hgroup : ∀ (u s : ℝ) (x : X), U u (U s x) = U (u + s) x)
    {epsMinus gamma : ℝ} {t u : ℝ} {Ct Su : ℕ}
    (hC : ∃ w : List Γ, w.length ≤ Ct ∧ dist (U t chi) (wordAct act w chi) ≤ epsMinus)
    (hS : ∃ w : List Γ, w.length ≤ Su ∧ ∀ x, dist (wordAct act w x) (U u x) ≤ gamma) :
    approxComplexity act chi (epsMinus + gamma) (U (u + t) chi) ≤ Ct + Su := by
  obtain ⟨w₁, hw₁, hd₁⟩ := hC
  obtain ⟨w₂, hw₂, hd₂⟩ := hS
  refine Nat.sInf_le ⟨w₂ ++ w₁, ?_, ?_⟩
  · rw [List.length_append]
    omega
  · rw [wordAct_append]
    have hstep : dist (U (u + t) chi) (U u (wordAct act w₁ chi)) ≤ epsMinus := by
      rw [← hgroup u t chi, (hUiso u).dist_eq]
      exact hd₁
    have htri := dist_triangle (U (u + t) chi) (U u (wordAct act w₁ chi))
      (wordAct act w₂ (wordAct act w₁ chi))
    have hsim : dist (U u (wordAct act w₁ chi)) (wordAct act w₂ (wordAct act w₁ chi)) ≤ gamma := by
      rw [dist_comm]
      exact hd₂ _
    linarith

/-! ## Theorem A: the continuous lower ramp -/

/-- **Geometric skeleton transfer.**  Hardness at one skeleton endpoint forces a linear lower bound
at every earlier time of its geometric cell. -/
theorem lt_approxComplexity_of_skeleton
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    (hgroup : ∀ (u s : ℝ) (x : X), U u (U s x) = U (u + s) x)
    {epsMinus epsPlus gamma v A c cq K t T : ℝ}
    (hgamma : gamma = epsPlus - epsMinus)
    (hv : 0 < v) (hA : 0 ≤ A)
    (hsim : ∀ u : ℝ, 0 ≤ u → ∃ w : List Γ, w.length ≤ ⌈v * u + A⌉₊ ∧
      ∀ x, dist (wordAct act w x) (U u x) ≤ gamma)
    (hCne : ∃ w : List Γ,
      dist (U t chi) (wordAct act w chi) ≤ epsMinus)
    (hhard : c * v * T - K < (approxComplexity act chi epsPlus (U T chi) : ℝ))
    (hle : t ≤ T) (hq : T ≤ cq * t) (hc : c * cq ≤ 1) :
    (1 - cq * (1 - c)) * v * t - (K + A + 1) <
      (approxComplexity act chi epsMinus (U t chi) : ℝ) := by
  classical
  set Ct : ℕ := approxComplexity act chi epsMinus (U t chi) with hCt
  set u : ℝ := T - t with hu
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  obtain ⟨wS, hwS, hdS⟩ := hsim u hu0
  obtain ⟨w₁, hd₁⟩ := hCne
  have hCwit : ∃ w : List Γ, w.length ≤ Ct ∧
      dist (U t chi) (wordAct act w chi) ≤ epsMinus := by
    have hmem : ({s : ℕ | ∃ w : List Γ, w.length ≤ s ∧
        dist (U t chi) (wordAct act w chi) ≤ epsMinus}).Nonempty :=
      ⟨w₁.length, w₁, le_rfl, hd₁⟩
    exact Nat.sInf_mem hmem
  have hcomp := approxComplexity_le_add_of_witnesses act chi U hUiso hgroup
    (t := t) (u := u) hCwit ⟨wS, hwS, hdS⟩
  have hut : u + t = T := by rw [hu]; ring
  have hgammaeq : epsMinus + gamma = epsPlus := by rw [hgamma]; ring
  rw [hut, hgammaeq] at hcomp
  have hcast : (approxComplexity act chi epsPlus (U T chi) : ℝ) ≤
      (Ct : ℝ) + (⌈v * u + A⌉₊ : ℝ) := by exact_mod_cast hcomp
  have hceil : (⌈v * u + A⌉₊ : ℝ) ≤ v * u + A + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ v * u + A)
    linarith
  have hTq : (1 - c) * v * T ≤ cq * (1 - c) * v * t := by
    rcases le_total c 1 with hc1 | hc1
    · have h1c : 0 ≤ 1 - c := by linarith
      nlinarith [hq, hv, h1c]
    · nlinarith [hq, hv, hc, hle]
  nlinarith [hhard, hcast, hceil, hv, hA]

/-! ## Theorem B: the matching upper ramp -/

/-- **Upper ramp from an easy seed.**  Composing a bounded preparation of the seed with a uniform
simulator gives a linear upper bound at every time. -/
theorem approxComplexity_le_of_easy_seed
    (act : Γ → X → X) (chi : X) (U : ℝ → X → X)
    (hUiso : ∀ u : ℝ, Isometry (U u))
    (hgroup : ∀ (u s : ℝ) (x : X), U u (U s x) = U (u + s) x)
    {eta delta : ℝ} {b Su : ℕ} {t : ℝ}
    (hseed : ∃ w : List Γ, w.length ≤ b ∧ dist chi (wordAct act w chi) ≤ eta)
    (hS : ∃ w : List Γ, w.length ≤ Su ∧ ∀ x, dist (wordAct act w x) (U t x) ≤ delta) :
    approxComplexity act chi (eta + delta) (U t chi) ≤ b + Su := by
  have h0 : U 0 chi = chi := by
    have h1 : U 0 (U 0 chi) = U 0 chi := by simpa using hgroup 0 0 chi
    exact (hUiso 0).injective h1
  obtain ⟨w, hw, hd⟩ := hseed
  have hC : ∃ w : List Γ, w.length ≤ b ∧ dist (U 0 chi) (wordAct act w chi) ≤ eta :=
    ⟨w, hw, by rw [h0]; exact hd⟩
  have hmain := approxComplexity_le_add_of_witnesses act chi U hUiso hgroup
    (epsMinus := eta) (gamma := delta) (t := 0) (u := t) hC hS
  simpa using hmain

/-! ## Theorem C: skeleton length and union bound -/

/-- **Geometric skeleton length.**  A geometric progression of ratio `q` starting at `T₀` and
truncated at `Tmax` has at most `2 + log (Tmax / T₀) / log q` terms. -/
theorem skeleton_card_le {T0 Tmax q : ℝ} (hT0 : 0 < T0) (hq : 1 < q) {N : ℕ}
    (hN : T0 * q ^ N ≤ Tmax) :
    (N : ℝ) + 1 ≤ 2 + Real.log (Tmax / T0) / Real.log q := by
  have hqpos : (0 : ℝ) < q := lt_trans zero_lt_one hq
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hTmax : 0 < Tmax := lt_of_lt_of_le (by positivity) hN
  have hratio : q ^ N ≤ Tmax / T0 := by
    rw [le_div_iff₀ hT0]
    linarith [hN]
  have hlog : (N : ℝ) * Real.log q ≤ Real.log (Tmax / T0) := by
    have hpow : Real.log (q ^ N) = (N : ℝ) * Real.log q := Real.log_pow N q
    rw [← hpow]
    exact Real.log_le_log (by positivity) hratio
  have : (N : ℝ) ≤ Real.log (Tmax / T0) / Real.log q := by
    rw [le_div_iff₀ hlogq]
    exact hlog
  linarith

/-- **Union bound over the skeleton.**  If each of `N + 1` skeleton events fails with probability
at most `B e^{-κ r}`, their union fails with probability at most `(N + 1) B e^{-κ r}`. -/
theorem skeleton_union_bound {N : ℕ} {p : ℕ → ℝ} {B kappa r : ℝ}
    (hp : ∀ j ≤ N, p j ≤ B * Real.exp (-(kappa * r))) :
    ∑ j ∈ Finset.range (N + 1), p j ≤ ((N : ℝ) + 1) * (B * Real.exp (-(kappa * r))) := by
  calc ∑ j ∈ Finset.range (N + 1), p j
      ≤ ∑ _j ∈ Finset.range (N + 1), B * Real.exp (-(kappa * r)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact hp j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ = ((N : ℝ) + 1) * (B * Real.exp (-(kappa * r))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **Sufficient replica order.**  Taking `r ≥ log (B (N+1) / δ) / κ` makes the skeleton union
failure probability at most `δ`. -/
theorem skeleton_replica_order {N : ℕ} {B kappa r delta : ℝ}
    (hB : 0 < B) (hkappa : 0 < kappa) (hdelta : 0 < delta)
    (hr : Real.log (B * ((N : ℝ) + 1) / delta) / kappa ≤ r) :
    ((N : ℝ) + 1) * (B * Real.exp (-(kappa * r))) ≤ delta := by
  have hpos : 0 < B * ((N : ℝ) + 1) / delta := by positivity
  have hlog : Real.log (B * ((N : ℝ) + 1) / delta) ≤ kappa * r := by
    rw [div_le_iff₀ hkappa] at hr
    linarith [hr]
  have hexp : B * ((N : ℝ) + 1) / delta ≤ Real.exp (kappa * r) := by
    calc B * ((N : ℝ) + 1) / delta
        = Real.exp (Real.log (B * ((N : ℝ) + 1) / delta)) := (Real.exp_log hpos).symm
      _ ≤ Real.exp (kappa * r) := Real.exp_le_exp.mpr hlog
  have hexppos : 0 < Real.exp (kappa * r) := Real.exp_pos _
  have hinv : Real.exp (-(kappa * r)) = (Real.exp (kappa * r))⁻¹ := by
    rw [Real.exp_neg]
  rw [hinv]
  rw [div_le_iff₀ hdelta] at hexp
  have hstep : ((N : ℝ) + 1) * B ≤ delta * Real.exp (kappa * r) := by linarith [hexp]
  calc ((N : ℝ) + 1) * (B * (Real.exp (kappa * r))⁻¹)
      = (((N : ℝ) + 1) * B) * (Real.exp (kappa * r))⁻¹ := by ring
    _ ≤ (delta * Real.exp (kappa * r)) * (Real.exp (kappa * r))⁻¹ := by
        exact mul_le_mul_of_nonneg_right hstep (by positivity)
    _ = delta := by field_simp

end

end HTGeometry
