import GaloisForLFunctions.GaloisTheoryOfZeros.TheTurnsGenerateTheForwardMonodromyGroup
import GaloisForLFunctions.GaloisTheoryOfZeros.TransportAlongRealTimesKeepsTheOrderOfTheZeros

/-!
# Conjugation of the zeros is the word of the turns around the real branch times

Over a positive real time `t` off the branch times the conjugation `c_t : z ↦ z̄` of the fibre is
an element of the forward monodromy group. This file writes it in the generators.

* **Conjugate paths.** Transport along the conjugate of a path between real times is the
  conjugate transport (`Transports.conj_path`). A segment of real times is its own conjugate.
* **The turn law** (`transports_upperHalfTurn_conj`). Let `θ` be the turn around a real time
  `p` based at `p + r²`, and `V` the transport over the upper half circle from `p − r²` to
  `p + r²`. The lower half circle is the conjugate of the upper one, so
  `c_{p−r²} = V⁻¹ ∘ (c_{p+r²} ∘ θ) ∘ V`: conjugation before `p` is conjugation after `p` times
  the turn.
* **One step** (`fibreConj_eq_permCongr_mul_turn`). If `[t, p − r²]` has no branch time and `W`
  is the transport from `t` along the real axis and over the upper half circle, then
  `c_t = W⁻¹ ∘ (c_{p+r²} ∘ θ) ∘ W`.
* **The word** (`exists_fibreConj_eq_prod_turnLassos`). Let `p₁ < … < p_m` be the real branch
  times above `t`. Then `c_t = λ_m ∘ ⋯ ∘ λ₁`, where `λ_j` is a lasso at `t` whose head is a turn
  of radius below `ε` around `p_j` and whose tail runs in the box
  `t ≤ Re τ ≤ 1/8`, `0 ≤ Im τ ≤ ε`. Each `λ_j` is one of the generating turn lassos
  (`IsUpperTurnLasso.mem_turnLassos`).
* **Conjugation inverts the turns around real times**
  (`fibreConj_mul_turnPerm_mul_fibreConj`): `c ∘ θ ∘ c = θ⁻¹`.
-/

open Complex Set Metric
open RHTower

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Conjugate paths -/

/-- Transport along a path that is pointwise the conjugate of `γ` is the conjugate transport. -/
theorem Transports.conj_path {γ γ' : ℝ → ℂ} {z w : ℂ} (h : Transports γ z w)
    (hc : ∀ s, γ' s = starRingEnd ℂ (γ s)) :
    Transports γ' (starRingEnd ℂ z) (starRingEnd ℂ w) := by
  have h' := h.conj
  rw [show (fun s => starRingEnd ℂ (γ s)) = γ' from funext fun s => (hc s).symm] at h'
  exact h'

/-- A segment of real times is its own conjugate. -/
theorem conj_timeSeg (t₁ t₂ s : ℝ) : timeSeg t₁ t₂ s = starRingEnd ℂ (timeSeg t₁ t₂ s) := by
  rw [timeSeg, Complex.conj_ofReal]

/-- A segment of positive real times without branch times is a forward path. -/
theorem isForwardPath_timeSeg_of_forall_not_mem {t₁ t₂ : ℝ} (h₁ : 0 < t₁) (h : t₁ ≤ t₂)
    (hb : ∀ u ∈ Icc t₁ t₂, (u : ℂ) ∉ branchTimes) : IsForwardPath (timeSeg t₁ t₂) := by
  have hmem : ∀ s ∈ Icc (0 : ℝ) 1, t₁ + s * (t₂ - t₁) ∈ Icc t₁ t₂ := fun s hs =>
    ⟨by linarith [mul_nonneg hs.1 (sub_nonneg.2 h)],
      by linarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 h)]⟩
  exact ⟨(Complex.continuous_ofReal.comp
      (by fun_prop : Continuous fun s : ℝ => t₁ + s * (t₂ - t₁))).continuousOn,
    fun s hs => by
      rw [timeSeg, Complex.ofReal_re]
      exact h₁.trans_le (hmem s hs).1,
    fun s hs => hb _ (hmem s hs)⟩

theorem fibreConj_mul_self (t : ℝ) : fibreConj t * fibreConj t = 1 :=
  Equiv.ext fun x => Subtype.ext (Complex.conj_conj x.1)

/-- **Without a real branch time above `t` the conjugation is trivial**: the segment to a time
beyond `1/8` carries every zero to a real zero, and its transport commutes with conjugation. -/
theorem fibreConj_eq_one_of_forall_not_mem {t : ℝ} (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes)
    (h : ∀ p : ℝ, t < p → (p : ℂ) ∉ branchTimes) : fibreConj t = 1 := by
  have hS : IsForwardPath (timeSeg t (max t (1 / 8))) :=
    isForwardPath_timeSeg_of_forall_not_mem ht (le_max_left _ _) fun u hu hub => by
      rcases eq_or_lt_of_le hu.1 with heq | hlt
      · rw [← heq] at hub
        exact hb hub
      · exact h u hlt hub
  refine Equiv.ext fun x => Subtype.ext ?_
  have hx := hS.transports_fibreEquiv (timeSeg_zero t _) (timeSeg_one t _) x
  have hreal := Complex.conj_eq_iff_im.2 (im_eq_zero_of_zero (le_max_right t (1 / 8))
    (hS.fibreEquiv (timeSeg_zero t _) (timeSeg_one t _) x).2)
  have hc := hx.conj_path (conj_timeSeg t (max t (1 / 8)))
  rw [hreal] at hc
  exact hS.transports_injective hc hx

/-! ## The circle around a real time -/

theorem turnPath_zero_ofReal (p r : ℝ) : turnPath (p : ℂ) r 0 = ((p + r ^ 2 : ℝ) : ℂ) := by
  rw [turnPath_zero, Complex.ofReal_add, Complex.ofReal_pow]

theorem turnPath_one_ofReal (p r : ℝ) : turnPath (p : ℂ) r 1 = ((p + r ^ 2 : ℝ) : ℂ) := by
  rw [turnPath_one, Complex.ofReal_add, Complex.ofReal_pow]

theorem turnPath_half_ofReal (p r : ℝ) : turnPath (p : ℂ) r (1 / 2) = ((p - r ^ 2 : ℝ) : ℂ) := by
  rw [turnPath_eq, show 2 * Real.pi * (1 / 2) = Real.pi by ring, Real.cos_pi, Real.sin_pi]
  push_cast
  ring

/-- The circle around a real time is symmetric in the real axis. -/
theorem conj_turnPath_ofReal (p r u : ℝ) :
    starRingEnd ℂ (turnPath (p : ℂ) r u) = turnPath (p : ℂ) r (1 - u) := by
  have hc : Real.cos (2 * Real.pi * (1 - u)) = Real.cos (2 * Real.pi * u) := by
    rw [show 2 * Real.pi * (1 - u) = 2 * Real.pi - 2 * Real.pi * u by ring, Real.cos_two_pi_sub]
  have hs : Real.sin (2 * Real.pi * (1 - u)) = -Real.sin (2 * Real.pi * u) := by
    rw [show 2 * Real.pi * (1 - u) = 2 * Real.pi - 2 * Real.pi * u by ring, Real.sin_two_pi_sub]
  rw [turnPath_eq, turnPath_eq, hc, hs, map_add, map_add, map_mul, Complex.conj_ofReal,
    Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The upper half of the circle around the real time `p`, from `p − r²` to `p + r²`. -/
def upperHalfTurn (p r : ℝ) : ℝ → ℂ := pathRev (subPath (turnPath (p : ℂ) r) 0 (1 / 2))

theorem upperHalfTurn_zero (p r : ℝ) : upperHalfTurn p r 0 = ((p - r ^ 2 : ℝ) : ℂ) := by
  rw [upperHalfTurn, pathRev_zero, subPath_one, turnPath_half_ofReal]

theorem upperHalfTurn_one (p r : ℝ) : upperHalfTurn p r 1 = ((p + r ^ 2 : ℝ) : ℂ) := by
  rw [upperHalfTurn, pathRev_one, subPath_zero, turnPath_zero_ofReal]

theorem isForwardPath_upperHalfTurn {p r : ℝ} (hT : IsForwardPath (turnPath (p : ℂ) r)) :
    IsForwardPath (upperHalfTurn p r) :=
  (hT.sub ⟨le_rfl, zero_le_one⟩ ⟨by norm_num, by norm_num⟩).reverse

/-- **The turn law.** If the upper half circle carries `q` to `w` and the turn carries `w` to
`w'`, then the upper half circle carries `q̄` to the conjugate of `w'`: the lower half circle
is the conjugate of the upper one. -/
theorem transports_upperHalfTurn_conj {p r : ℝ} (hT : IsForwardPath (turnPath (p : ℂ) r))
    {q w w' : ℂ} (h1 : Transports (upperHalfTurn p r) q w)
    (h2 : Transports (turnPath (p : ℂ) r) w w') :
    Transports (upperHalfTurn p r) (starRingEnd ℂ q) (starRingEnd ℂ w') := by
  obtain ⟨z, hz, rfl, rfl⟩ := h2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h1' : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hA : Transports (upperHalfTurn p r) (z (1 / 2)) (z 0) :=
    (hz.transports_subPath h0 hh).symm
  have hq : q = z (1 / 2) := (isForwardPath_upperHalfTurn hT).transports_injective h1 hA
  rw [hq]
  refine (hz.transports_subPath hh h1').conj_path fun s => ?_
  rw [subPath, conj_turnPath_ofReal, upperHalfTurn, pathRev, subPath]
  congr 1
  ring

/-! ## The path over a real time -/

/-- The path from the real time `t` along the real axis to `p − r²` and over the upper half
circle to `p + r²`. -/
def overPath (t p r : ℝ) : ℝ → ℂ := pathJoin (timeSeg t (p - r ^ 2)) (upperHalfTurn p r)

theorem overPath_zero (t p r : ℝ) : overPath t p r 0 = (t : ℂ) := by
  rw [overPath, pathJoin_zero, timeSeg_zero]

theorem overPath_one (t p r : ℝ) : overPath t p r 1 = ((p + r ^ 2 : ℝ) : ℂ) := by
  rw [overPath, pathJoin_one, upperHalfTurn_one]

theorem isForwardPath_overPath {t p r : ℝ} (hS : IsForwardPath (timeSeg t (p - r ^ 2)))
    (hT : IsForwardPath (turnPath (p : ℂ) r)) : IsForwardPath (overPath t p r) :=
  hS.join (isForwardPath_upperHalfTurn hT)
    ((timeSeg_one _ _).trans (upperHalfTurn_zero p r).symm)

/-- If the path over `p` carries `x` to `w` and the turn carries `w` to `w'`, the path over `p`
carries `x̄` to the conjugate of `w'`. -/
theorem transports_overPath_conj {t p r : ℝ} (hS : IsForwardPath (timeSeg t (p - r ^ 2)))
    (hT : IsForwardPath (turnPath (p : ℂ) r)) {x w w' : ℂ}
    (h1 : Transports (overPath t p r) x w) (h2 : Transports (turnPath (p : ℂ) r) w w') :
    Transports (overPath t p r) (starRingEnd ℂ x) (starRingEnd ℂ w') := by
  have hV := isForwardPath_upperHalfTurn hT
  have hx : complexHeat (timeSeg t (p - r ^ 2) 0) x = 0 := by
    have := h1.zero_left
    rw [overPath_zero] at this
    rw [timeSeg_zero]
    exact this
  obtain ⟨m, hm⟩ := hS.exists_transports hx
  have hm0 : complexHeat (upperHalfTurn p r 0) m = 0 := by
    have := hm.zero_right
    rw [timeSeg_one] at this
    rw [upperHalfTurn_zero]
    exact this
  obtain ⟨w₂, hw₂⟩ := hV.exists_transports hm0
  have hw : w₂ = w := (isForwardPath_overPath hS hT).transports_unique (hm.trans hw₂) h1
  rw [hw] at hw₂
  exact (hm.conj_path (conj_timeSeg t (p - r ^ 2))).trans
    (transports_upperHalfTurn_conj hT hw₂ h2)

/-- The transport along the path over `p`. -/
def overEquiv {t p r : ℝ} (hS : IsForwardPath (timeSeg t (p - r ^ 2)))
    (hT : IsForwardPath (turnPath (p : ℂ) r)) :
    Fibre (t : ℂ) ≃ Fibre ((p + r ^ 2 : ℝ) : ℂ) :=
  (isForwardPath_overPath hS hT).fibreEquiv (overPath_zero t p r) (overPath_one t p r)

/-- The turn around the real time `p` as a permutation of the fibre over `p + r²`. -/
def turnPerm {p r : ℝ} (hT : IsForwardPath (turnPath (p : ℂ) r)) :
    Equiv.Perm (Fibre ((p + r ^ 2 : ℝ) : ℂ)) :=
  hT.fibreEquiv (turnPath_zero_ofReal p r) (turnPath_one_ofReal p r)

/-- **One step of the word.** Conjugation at `t` is conjugation at `p + r²` times the turn
around `p`, carried back along the path over `p`. -/
theorem fibreConj_eq_permCongr_mul_turn {t p r : ℝ}
    (hS : IsForwardPath (timeSeg t (p - r ^ 2))) (hT : IsForwardPath (turnPath (p : ℂ) r)) :
    fibreConj t =
      (overEquiv hS hT).symm.permCongrHom (fibreConj (p + r ^ 2) * turnPerm hT) := by
  refine Equiv.ext fun x => ?_
  change fibreConj t x =
    (overEquiv hS hT).symm.permCongr (fibreConj (p + r ^ 2) * turnPerm hT) x
  rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.eq_symm_apply]
  refine IsForwardPath.fibreEquiv_eq _ _ _ ?_
  exact transports_overPath_conj hS hT
    (IsForwardPath.transports_fibreEquiv _ _ _ x)
    (hT.transports_fibreEquiv (turnPath_zero_ofReal p r) (turnPath_one_ofReal p r) _)

/-- **Conjugation times a turn around a real time is an involution.** -/
theorem fibreConj_mul_turnPerm_mul_self {p r : ℝ} (hT : IsForwardPath (turnPath (p : ℂ) r)) :
    fibreConj (p + r ^ 2) * turnPerm hT * (fibreConj (p + r ^ 2) * turnPerm hT) = 1 := by
  have hh : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hpos : 0 < p - r ^ 2 := by
    have := hT.re_pos _ hh
    rwa [turnPath_half_ofReal, Complex.ofReal_re] at this
  have hnb : ((p - r ^ 2 : ℝ) : ℂ) ∉ branchTimes := by
    have := hT.simple _ hh
    rwa [turnPath_half_ofReal] at this
  have hS : IsForwardPath (timeSeg (p - r ^ 2) (p - r ^ 2)) :=
    isForwardPath_timeSeg_of_forall_not_mem hpos le_rfl fun u hu hub => by
      rw [le_antisymm hu.2 hu.1] at hub
      exact hnb hub
  apply (overEquiv hS hT).symm.permCongrHom.injective
  rw [map_mul, map_one, ← fibreConj_eq_permCongr_mul_turn hS hT]
  exact fibreConj_mul_self _

/-- **Conjugation inverts the turn around a real time**: `c ∘ θ ∘ c = θ⁻¹`. -/
theorem fibreConj_mul_turnPerm_mul_fibreConj {p r : ℝ}
    (hT : IsForwardPath (turnPath (p : ℂ) r)) :
    fibreConj (p + r ^ 2) * turnPerm hT * fibreConj (p + r ^ 2) = (turnPerm hT)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by
    rw [mul_assoc]
    exact fibreConj_mul_turnPerm_mul_self hT)

/-! ## Lassos with tails above the real axis -/

/-- The lasso with tail `δ` from `b` to `x` and head the loop `T` at `x`: the permutation
`U_δ⁻¹ ∘ U_T ∘ U_δ` of the fibre over `b`. -/
def lassoPerm {δ T : ℝ → ℂ} (hδ : IsForwardPath δ) (hT : IsForwardPath T) {b x : ℂ}
    (d0 : δ 0 = b) (d1 : δ 1 = x) (T0 : T 0 = x) (T1 : T 1 = x) : Equiv.Perm (Fibre b) :=
  ((hδ.fibreEquiv d0 d1).trans (hT.fibreEquiv T0 T1)).trans (hδ.fibreEquiv d0 d1).symm

theorem lassoPerm_congr {δ T : ℝ → ℂ} (hδ : IsForwardPath δ) (hT : IsForwardPath T)
    {b x x' : ℂ} (e : x = x') (d0 : δ 0 = b) (d1 : δ 1 = x) (T0 : T 0 = x) (T1 : T 1 = x)
    (d1' : δ 1 = x') (T0' : T 0 = x') (T1' : T 1 = x') :
    lassoPerm hδ hT d0 d1 T0 T1 = lassoPerm hδ hT d0 d1' T0' T1' := by
  subst e
  rfl

/-- The box of times that holds the tails of the lassos at `t`. -/
def tailBox (t ε : ℝ) : Set ℂ := {τ | t ≤ τ.re ∧ τ.re ≤ 1 / 8 ∧ 0 ≤ τ.im ∧ τ.im ≤ ε}

/-- `σ` is a lasso at the real time `t` around the real time `p`: its head is the turn of a
radius `r² < ε²` around `p` and its tail runs from `t` to `p + r²` inside `tailBox t ε`. -/
def IsUpperTurnLasso (t ε p : ℝ) (σ : Equiv.Perm (Fibre (t : ℂ))) : Prop :=
  ∃ (r : ℝ) (δ : ℝ → ℂ) (hδ : IsForwardPath δ) (d0 : δ 0 = (t : ℂ))
    (d1 : δ 1 = ((p + r ^ 2 : ℝ) : ℂ)) (hT : IsForwardPath (turnPath (p : ℂ) r)),
    0 < r ∧ r < ε ∧ (∀ s ∈ Icc (0 : ℝ) 1, δ s ∈ tailBox t ε) ∧
      σ = lassoPerm hδ hT d0 d1 (turnPath_zero_ofReal p r) (turnPath_one_ofReal p r)

/-- A lasso around a real branch time is one of the generating turn lassos. -/
theorem IsUpperTurnLasso.mem_turnLassos {t ε p : ℝ} {σ : Equiv.Perm (Fibre (t : ℂ))}
    (h : IsUpperTurnLasso t ε p σ) (hp : (p : ℂ) ∈ branchTimes) : σ ∈ turnLassos (t : ℂ) := by
  obtain ⟨r, δ, hδ, d0, d1, hT, -, -, -, rfl⟩ := h
  have e : ((p + r ^ 2 : ℝ) : ℂ) = (p : ℂ) + (r : ℂ) ^ 2 := by
    rw [Complex.ofReal_add, Complex.ofReal_pow]
  exact ⟨(p : ℂ), r, δ, hδ, d0, d1.trans e, hT, hp,
    lassoPerm_congr hδ hT e d0 d1 _ _ (d1.trans e) (turnPath_zero _ r) (turnPath_one _ r)⟩

/-- A lasso at `s₁` carried back along a path from `t` inside the box is a lasso at `t`. -/
theorem IsUpperTurnLasso.pullback {t s₁ ε p : ℝ} {η : ℝ → ℂ} (hη : IsForwardPath η)
    (e0 : η 0 = (t : ℂ)) (e1 : η 1 = (s₁ : ℂ)) (hts : t ≤ s₁)
    (hbox : ∀ s ∈ Icc (0 : ℝ) 1, η s ∈ tailBox t ε) {σ : Equiv.Perm (Fibre (s₁ : ℂ))}
    (h : IsUpperTurnLasso s₁ ε p σ) :
    IsUpperTurnLasso t ε p ((hη.fibreEquiv e0 e1).symm.permCongrHom σ) := by
  obtain ⟨r, δ, hδ, d0, d1, hT, hr, hrε, hδbox, rfl⟩ := h
  have hj := hη.join hδ (e1.trans d0.symm)
  have j0 : pathJoin η δ 0 = (t : ℂ) := (pathJoin_zero η δ).trans e0
  have j1 : pathJoin η δ 1 = ((p + r ^ 2 : ℝ) : ℂ) := (pathJoin_one η δ).trans d1
  refine ⟨r, pathJoin η δ, hj, j0, j1, hT, hr, hrε, pathJoin_mem hbox fun s hs => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hδbox s hs
    exact ⟨hts.trans h1, h2, h3, h4⟩
  · unfold lassoPerm
    rw [hη.fibreEquiv_join hδ e0 e1 d0 d1 hj j0 j1]
    rfl

theorem upperHalfTurn_mem_tailBox {t p r ε : ℝ} (h₁ : t ≤ p - r ^ 2) (h₂ : p + r ^ 2 ≤ 1 / 8)
    (h₃ : r ^ 2 ≤ ε) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : upperHalfTurn p r s ∈ tailBox t ε := by
  have hr : 0 ≤ r ^ 2 := sq_nonneg r
  have hre : (upperHalfTurn p r s).re =
      p + r ^ 2 * Real.cos (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s))) := by
    rw [upperHalfTurn, pathRev, subPath, turnPath_re, Complex.ofReal_re]
  have him : (upperHalfTurn p r s).im =
      r ^ 2 * Real.sin (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s))) := by
    rw [upperHalfTurn, pathRev, subPath, turnPath_im, Complex.ofReal_im, zero_add]
  have hx0 : 0 ≤ 2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s)) := by
    linarith [mul_nonneg Real.pi_pos.le (sub_nonneg.2 hs.2)]
  have hx1 : 2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s)) ≤ Real.pi := by
    linarith [mul_nonneg Real.pi_pos.le hs.1]
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi hx0 hx1
  have hsin' := Real.sin_le_one (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s)))
  have hc := Real.neg_one_le_cos (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s)))
  have hc' := Real.cos_le_one (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hre]
    nlinarith [mul_nonneg hr (by linarith : (0 : ℝ) ≤
      Real.cos (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s))) + 1)]
  · rw [hre]
    nlinarith [mul_nonneg hr (by linarith : (0 : ℝ) ≤
      1 - Real.cos (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s))))]
  · rw [him]
    exact mul_nonneg hr hsin
  · rw [him]
    nlinarith [mul_nonneg hr (by linarith : (0 : ℝ) ≤
      1 - Real.sin (2 * Real.pi * (0 + (1 / 2 - 0) * (1 - s))))]

theorem overPath_mem_tailBox {t p r ε : ℝ} (h₁ : t ≤ p - r ^ 2) (h₂ : p + r ^ 2 ≤ 1 / 8)
    (hε : 0 ≤ ε) (h₃ : r ^ 2 ≤ ε) : ∀ s ∈ Icc (0 : ℝ) 1, overPath t p r s ∈ tailBox t ε :=
  pathJoin_mem (fun s hs => by
    have hs1 : t ≤ t + s * (p - r ^ 2 - t) := by
      linarith [mul_nonneg hs.1 (sub_nonneg.2 h₁)]
    have hs2 : t + s * (p - r ^ 2 - t) ≤ p - r ^ 2 := by
      linarith [mul_nonneg (sub_nonneg.2 hs.2) (sub_nonneg.2 h₁)]
    have hre : (timeSeg t (p - r ^ 2) s).re = t + s * (p - r ^ 2 - t) := by
      rw [timeSeg, Complex.ofReal_re]
    have him : (timeSeg t (p - r ^ 2) s).im = 0 := by rw [timeSeg, Complex.ofReal_im]
    exact ⟨hre.ge.trans' hs1, by rw [hre]; linarith [sq_nonneg r], him.ge, him.le.trans hε⟩)
    fun s hs => upperHalfTurn_mem_tailBox h₁ h₂ h₃ hs

/-- The turn around `p` carried back along the path over `p` is a lasso at `t`. -/
theorem isUpperTurnLasso_turn {t p r ε : ℝ} (hS : IsForwardPath (timeSeg t (p - r ^ 2)))
    (hT : IsForwardPath (turnPath (p : ℂ) r)) (hr : 0 < r) (hrε : r < ε)
    (hbox : ∀ s ∈ Icc (0 : ℝ) 1, overPath t p r s ∈ tailBox t ε) :
    IsUpperTurnLasso t ε p ((overEquiv hS hT).symm.permCongrHom (turnPerm hT)) :=
  ⟨r, overPath t p r, isForwardPath_overPath hS hT, overPath_zero t p r, overPath_one t p r, hT,
    hr, hrε, hbox, rfl⟩

/-! ## The word -/

/-- The word for a given increasing list of the real branch times above `t`. -/
theorem exists_turnLassos_of_list {ε : ℝ} (hε : 0 < ε) :
    ∀ (ps : List ℝ) (t : ℝ), 0 < t → (t : ℂ) ∉ branchTimes → ps.Pairwise (· < ·) →
      (∀ p : ℝ, p ∈ ps ↔ t < p ∧ (p : ℂ) ∈ branchTimes) →
      ∃ l : List (ℝ × Equiv.Perm (Fibre (t : ℂ))), l.map Prod.fst = ps ∧
        (∀ x ∈ l, IsUpperTurnLasso t ε x.1 x.2) ∧
        fibreConj t = (l.map Prod.snd).reverse.prod := by
  intro ps
  induction ps with
  | nil =>
    intro t ht hb _ hmem
    refine ⟨[], rfl, fun x hx => absurd hx List.not_mem_nil, ?_⟩
    rw [List.map_nil, List.reverse_nil, List.prod_nil]
    exact fibreConj_eq_one_of_forall_not_mem ht hb fun p hp hpb =>
      List.not_mem_nil ((hmem p).2 ⟨hp, hpb⟩)
  | cons p₁ ps ih =>
    intro t ht hb hpw hmem
    obtain ⟨hmin, hpw'⟩ := List.pairwise_cons.1 hpw
    obtain ⟨htp, hpb⟩ := (hmem p₁).1 List.mem_cons_self
    have hp8 : p₁ < 1 / 8 := by
      by_contra hcon
      exact ofReal_not_mem_branchTimes_of_eighth_le (not_lt.1 hcon) hpb
    have hp0 : 0 < ((p₁ : ℝ) : ℂ).re := by
      rw [Complex.ofReal_re]
      exact ht.trans htp
    obtain ⟨r₀, hr₀, hturn⟩ := exists_isForwardPath_turnPath hp0
    obtain ⟨ρ, hρ, hiso⟩ := exists_ball_branchTimes_subset hp0
    -- a radius below all the scales
    obtain ⟨r, hr, hr1, hr2, hr3, hr4, hr5, hr6⟩ : ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ r < ε ∧ r < 1 ∧
        r < p₁ - t ∧ r < ρ ∧ r < 1 / 8 - p₁ := by
      have hm : 0 < min r₀ (min ε (min 1 (min (p₁ - t) (min ρ (1 / 8 - p₁))))) :=
        lt_min hr₀ (lt_min hε (lt_min one_pos (lt_min (sub_pos.2 htp)
          (lt_min hρ (sub_pos.2 hp8)))))
      obtain ⟨m, hm0, hmlt⟩ : ∃ m : ℝ, 0 < m ∧
          m < min r₀ (min ε (min 1 (min (p₁ - t) (min ρ (1 / 8 - p₁))))) :=
        ⟨_, half_pos hm, half_lt_self hm⟩
      simp only [lt_min_iff] at hmlt
      exact ⟨m, hm0, hmlt⟩
    have hrr : r ^ 2 < r := by nlinarith
    have hT := hturn r ⟨hr, hr1⟩
    have hS : IsForwardPath (timeSeg t (p₁ - r ^ 2)) :=
      isForwardPath_timeSeg_of_forall_not_mem ht (by linarith) fun u hu hub => by
        rcases eq_or_lt_of_le hu.1 with heq | hlt
        · rw [← heq] at hub
          exact hb hub
        · rcases List.mem_cons.1 ((hmem u).2 ⟨hlt, hub⟩) with h | h
          · linarith [hu.2, pow_pos hr 2]
          · linarith [hmin u h, hu.2, sq_nonneg r]
    have hs₁pos : 0 < p₁ + r ^ 2 := add_pos_of_pos_of_nonneg (ht.trans htp) (sq_nonneg r)
    have hs₁b : ((p₁ + r ^ 2 : ℝ) : ℂ) ∉ branchTimes := by
      have := hT.simple 0 ⟨le_rfl, zero_le_one⟩
      rwa [turnPath_zero_ofReal] at this
    -- the real branch times above `p₁ + r²` are the rest of the list
    have hmem' : ∀ p : ℝ, p ∈ ps ↔ p₁ + r ^ 2 < p ∧ (p : ℂ) ∈ branchTimes := by
      intro p
      constructor
      · intro hp
        have hpb' := ((hmem p).1 (List.mem_cons_of_mem _ hp)).2
        refine ⟨?_, hpb'⟩
        by_contra hcon
        have hlt := hmin p hp
        have hball : (p : ℂ) ∈ ball ((p₁ : ℝ) : ℂ) ρ := by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (sub_pos.2 hlt)]
          linarith [not_lt.1 hcon]
        exact hlt.ne' (Complex.ofReal_injective (hiso _ hball hpb'))
      · rintro ⟨hp, hpb'⟩
        rcases List.mem_cons.1 ((hmem p).2 ⟨by linarith [sq_nonneg r], hpb'⟩) with h | h
        · exfalso
          linarith [sq_nonneg r]
        · exact h
    obtain ⟨l', hl'fst, hl'lasso, hl'prod⟩ := ih (p₁ + r ^ 2) hs₁pos hs₁b hpw' hmem'
    have hbox := overPath_mem_tailBox (t := t) (p := p₁) (r := r) (ε := ε) (by linarith)
      (by linarith) hε.le (by linarith)
    refine ⟨(p₁, (overEquiv hS hT).symm.permCongrHom (turnPerm hT)) ::
      l'.map fun x => (x.1, (overEquiv hS hT).symm.permCongrHom x.2), ?_, ?_, ?_⟩
    · rw [List.map_cons, List.map_map, ← hl'fst]
      rfl
    · intro x hx
      rcases List.mem_cons.1 hx with h | h
      · rw [h]
        exact isUpperTurnLasso_turn hS hT hr hr2 hbox
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 h
        exact (hl'lasso y hy).pullback (isForwardPath_overPath hS hT) (overPath_zero t p₁ r)
          (overPath_one t p₁ r) (by linarith [sq_nonneg r]) hbox
    · have hsnd : (l'.map fun x => (x.1, (overEquiv hS hT).symm.permCongrHom x.2)).map Prod.snd =
          (l'.map Prod.snd).map (overEquiv hS hT).symm.permCongrHom := by
        rw [List.map_map, List.map_map]
        rfl
      have hrev : ((l'.map Prod.snd).map (overEquiv hS hT).symm.permCongrHom).reverse =
          (l'.map Prod.snd).reverse.map (overEquiv hS hT).symm.permCongrHom := by
        simp only [List.map_reverse]
      rw [List.map_cons, hsnd, List.reverse_cons, hrev, List.prod_append, List.prod_singleton,
        ← map_list_prod, ← hl'prod]
      exact (fibreConj_eq_permCongr_mul_turn hS hT).trans (map_mul _ _ _)

/-- **Conjugation of the zeros is the word of the turns around the real branch times.** Over a
positive real time `t` off the branch times, let `p₁ < … < p_m` be the real branch times above
`t`. For every `ε > 0` there are lassos `λ_j` at `t` around `p_j`, with heads of radius below `ε`
and tails in `tailBox t ε`, such that `c_t = λ_m ∘ ⋯ ∘ λ₁`. -/
theorem exists_fibreConj_eq_prod_turnLassos {t : ℝ} (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ l : List (ℝ × Equiv.Perm (Fibre (t : ℂ))),
      (l.map Prod.fst).Pairwise (· < ·) ∧
      (∀ p : ℝ, p ∈ l.map Prod.fst ↔ t < p ∧ (p : ℂ) ∈ branchTimes) ∧
      (∀ x ∈ l, IsUpperTurnLasso t ε x.1 x.2) ∧
      fibreConj t = (l.map Prod.snd).reverse.prod := by
  have hfin : {p : ℝ | t < p ∧ (p : ℂ) ∈ branchTimes}.Finite := by
    refine ((finite_branchTimes_box (t₀ := t) (1 / 8) ht).preimage
      Complex.ofReal_injective.injOn).subset fun p hp => ?_
    have hp8 : p < 1 / 8 := by
      by_contra hcon
      exact ofReal_not_mem_branchTimes_of_eighth_le (not_lt.1 hcon) hp.2
    change (p : ℂ) ∈ branchTimes ∧ t ≤ (p : ℂ).re ∧ ‖(p : ℂ)‖ ≤ 1 / 8
    refine ⟨hp.2, ?_, ?_⟩
    · rw [Complex.ofReal_re]
      exact hp.1.le
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ht.trans hp.1)]
      exact hp8.le
  have hmem : ∀ p : ℝ, p ∈ hfin.toFinset.sort ↔ t < p ∧ (p : ℂ) ∈ branchTimes := fun p => by
    rw [Finset.mem_sort, Set.Finite.mem_toFinset]
    rfl
  obtain ⟨l, hl, hlasso, hprod⟩ := exists_turnLassos_of_list hε hfin.toFinset.sort t ht hb
    (Finset.sortedLT_sort _).pairwise hmem
  refine ⟨l, ?_, ?_, hlasso, hprod⟩
  · rw [hl]
    exact (Finset.sortedLT_sort _).pairwise
  · rw [hl]
    exact hmem

/-- The lassos at `t` around the real branch times above `t`. -/
def realTurnLassos (t ε : ℝ) : Set (Equiv.Perm (Fibre (t : ℂ))) :=
  {σ | ∃ p : ℝ, t < p ∧ (p : ℂ) ∈ branchTimes ∧ IsUpperTurnLasso t ε p σ}

theorem realTurnLassos_subset_turnLassos (t ε : ℝ) : realTurnLassos t ε ⊆ turnLassos (t : ℂ) :=
  fun _ ⟨_, _, hp, h⟩ => h.mem_turnLassos hp

/-- **Conjugation lies in the group generated by the turns around the real branch times above
the base time.** -/
theorem fibreConj_mem_closure_realTurnLassos {t : ℝ} (ht : 0 < t) (hb : (t : ℂ) ∉ branchTimes)
    {ε : ℝ} (hε : 0 < ε) : fibreConj t ∈ Subgroup.closure (realTurnLassos t ε) := by
  obtain ⟨l, -, hmem, hlasso, hprod⟩ := exists_fibreConj_eq_prod_turnLassos ht hb hε
  rw [hprod]
  refine Subgroup.list_prod_mem _ fun σ hσ => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hσ)
  obtain ⟨hx1, hx2⟩ := (hmem x.1).1 (List.mem_map_of_mem hx)
  exact Subgroup.subset_closure ⟨x.1, hx1, hx2, hlasso x hx⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
