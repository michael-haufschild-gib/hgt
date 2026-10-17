import GaloisForLFunctions.HTGeometry.DiscHolomorphicFixedPoint
import Mathlib.Data.Finset.Image

/-!
# Analytic Markov systems: inverse branches, admissible words and periodic orbits

An analytic Markov system (`System`) is the inverse-branch data of a real-analytic, orientation-
preserving, expanding Markov map `T`: `p` Markov discs `D_a = D̄(c_a, R_a)` with real centres, and `q`
holomorphic inverse branches `φ_e : D_{src e} → D_{tgt e}` with `φ_e(D_{src e}) ⊆ D̄(c_{tgt e}, θR_{tgt e})`,
`θ < 1` (the condition that makes the transfer operators nuclear), commuting with complex conjugation
(real-analyticity), with a holomorphic logarithm `ℓ_e` of `φ_e′` real on the real axis (orientation
preservation) and `φ_e′ ≤ κ < 1` on real points (expansion of `T`).

* `paths S a m`: the admissible words `e₁ ⋯ e_m` from state `a` (`src e₁ = a`, `tgt e_k = src e_{k+1}`).
* `compφ P = φ_{e_m} ∘ ⋯ ∘ φ_{e₁}`, `compΛ P z = Σ_k ℓ_{e_k}(z_k)` along the orbit.
* `mapsTo_compφ`, `differentiableOn_compφ`, `exp_compΛ` (chain rule `exp Λ = Φ′`), `compφ_conj`.
* A closed word (`endState = a`) has a unique fixed point `fixPt` in `D_a` (`isFixPt_fixPt`,
  `fixPt_unique`), which is real (`fixPt_real`), with `Λ` real and `exp Λ ≤ κ^m`
  (`compΛ_fixPt_im`, `exp_re_compΛ_fixPt_le`).  The words of length `m` closed at their start state
  are exactly the periodic points of `T^m` with their itineraries.
-/

open Complex Metric Set Filter
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AnalyticMarkov

/-- An analytic Markov system. -/
structure System where
  p : ℕ
  q : ℕ
  src : Fin q → Fin p
  tgt : Fin q → Fin p
  c : Fin p → ℝ
  R : Fin p → ℝ
  θ : ℝ
  κ : ℝ
  φ : Fin q → ℂ → ℂ
  ℓ : Fin q → ℂ → ℂ
  p_pos : 0 < p
  R_pos : ∀ a, 0 < R a
  θ_nonneg : 0 ≤ θ
  θ_lt_one : θ < 1
  κ_lt_one : κ < 1
  φ_diff : ∀ e, DifferentiableOn ℂ (φ e) (closedBall (c (src e) : ℂ) (R (src e)))
  φ_maps : ∀ e, MapsTo (φ e) (closedBall (c (src e) : ℂ) (R (src e)))
    (closedBall (c (tgt e) : ℂ) (θ * R (tgt e)))
  ℓ_diff : ∀ e, DifferentiableOn ℂ (ℓ e) (closedBall (c (src e) : ℂ) (R (src e)))
  ℓ_exp : ∀ e, ∀ z ∈ ball (c (src e) : ℂ) (R (src e)), Complex.exp (ℓ e z) = deriv (φ e) z
  φ_conj : ∀ e, ∀ z ∈ closedBall (c (src e) : ℂ) (R (src e)), φ e (conj z) = conj (φ e z)
  ℓ_conj : ∀ e, ∀ z ∈ closedBall (c (src e) : ℂ) (R (src e)), ℓ e (conj z) = conj (ℓ e z)
  expanding : ∀ e, ∀ x : ℝ, (x : ℂ) ∈ closedBall (c (src e) : ℂ) (θ * R (src e)) →
    Real.exp (ℓ e x).re ≤ κ

namespace System

variable (S : System)

/-- The closed Markov disc of a state. -/
def disc (a : Fin S.p) : Set ℂ := closedBall (S.c a : ℂ) (S.R a)

/-- The admissible words of length `m` from the state `a`. -/
def paths : Fin S.p → ℕ → Finset (List (Fin S.q))
  | _, 0 => {[]}
  | a, m + 1 => (Finset.univ.filter fun e => S.src e = a).biUnion fun e =>
      (paths (S.tgt e) m).image (e :: ·)

/-- The final state of a word. -/
def endState : Fin S.p → List (Fin S.q) → Fin S.p
  | a, [] => a
  | _, e :: P => endState (S.tgt e) P

/-- The composite inverse branch `φ_{e_m} ∘ ⋯ ∘ φ_{e₁}`. -/
def compφ : List (Fin S.q) → ℂ → ℂ
  | [] => id
  | e :: P => compφ P ∘ S.φ e

/-- The logarithmic derivative of the composite, `Σ_k ℓ_{e_k}(z_k)`. -/
def compΛ : List (Fin S.q) → ℂ → ℂ
  | [] => fun _ => 0
  | e :: P => fun z => S.ℓ e z + compΛ P (S.φ e z)

variable {S}

theorem mem_paths_succ {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} :
    P ∈ S.paths a (m + 1) ↔ ∃ e P', P = e :: P' ∧ S.src e = a ∧ P' ∈ S.paths (S.tgt e) m := by
  simp only [paths, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨e, he, P', hP', rfl⟩; exact ⟨e, P', rfl, he, hP'⟩
  · rintro ⟨e, P', rfl, he, hP'⟩; exact ⟨e, he, P', hP', rfl⟩

theorem length_of_mem_paths {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : P ∈ S.paths a m) :
    P.length = m := by
  induction m generalizing a P with
  | zero => simp [paths] at hP; simp [hP]
  | succ m ih =>
    obtain ⟨e, P', rfl, -, hP'⟩ := mem_paths_succ.mp hP
    simp [ih hP']

theorem θ_mul_le (a : Fin S.p) : S.θ * S.R a ≤ S.R a := by
  have := S.R_pos a
  nlinarith [S.θ_lt_one]

theorem closedBall_θ_subset_ball (a : Fin S.p) :
    closedBall (S.c a : ℂ) (S.θ * S.R a) ⊆ ball (S.c a : ℂ) (S.R a) :=
  closedBall_subset_ball (by have := S.R_pos a; nlinarith [S.θ_lt_one])

/-- **The composite maps the start disc into the end disc**, into the `θ`-subdisc for a nonempty
word. -/
theorem mapsTo_compφ {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : P ∈ S.paths a m) :
    MapsTo (S.compφ P) (S.disc a) (S.disc (S.endState a P)) ∧
      (m ≠ 0 → MapsTo (S.compφ P) (S.disc a)
        (closedBall (S.c (S.endState a P) : ℂ) (S.θ * S.R (S.endState a P)))) := by
  induction m generalizing a P with
  | zero =>
    simp only [paths, Finset.mem_singleton] at hP
    subst hP
    exact ⟨fun z hz => hz, fun h => absurd rfl h⟩
  | succ m ih =>
    obtain ⟨e, P', rfl, he, hP'⟩ := mem_paths_succ.mp hP
    subst he
    have h1 : MapsTo (S.φ e) (S.disc (S.src e)) (S.disc (S.tgt e)) := fun z hz =>
      closedBall_subset_closedBall (S.θ_mul_le _) (S.φ_maps e hz)
    obtain ⟨ih1, ih2⟩ := ih hP'
    refine ⟨ih1.comp h1, fun _ => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [paths, Finset.mem_singleton] at hP'
      subst hP'
      exact S.φ_maps e
    · exact (fun z hz => closedBall_subset_closedBall (le_refl _) ((ih2 hm.ne') (h1 hz)))

theorem endState_cons (a : Fin S.p) (e : Fin S.q) (P : List (Fin S.q)) :
    S.endState a (e :: P) = S.endState (S.tgt e) P := rfl

/-- **The composite and its logarithmic derivative are holomorphic** on the closed start disc. -/
theorem differentiableOn_compφ {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)}
    (hP : P ∈ S.paths a m) :
    DifferentiableOn ℂ (S.compφ P) (S.disc a) ∧ DifferentiableOn ℂ (S.compΛ P) (S.disc a) := by
  induction m generalizing a P with
  | zero =>
    simp only [paths, Finset.mem_singleton] at hP
    subst hP
    exact ⟨differentiableOn_id, differentiableOn_const _⟩
  | succ m ih =>
    obtain ⟨e, P', rfl, he, hP'⟩ := mem_paths_succ.mp hP
    subst he
    obtain ⟨ih1, ih2⟩ := ih hP'
    have hmaps : MapsTo (S.φ e) (S.disc (S.src e)) (S.disc (S.tgt e)) := fun z hz =>
      closedBall_subset_closedBall (S.θ_mul_le _) (S.φ_maps e hz)
    exact ⟨ih1.comp (S.φ_diff e) hmaps, (S.ℓ_diff e).add (ih2.comp (S.φ_diff e) hmaps)⟩

theorem compφ_cons (e : Fin S.q) (P : List (Fin S.q)) (z : ℂ) :
    S.compφ (e :: P) z = S.compφ P (S.φ e z) := rfl

theorem compΛ_cons (e : Fin S.q) (P : List (Fin S.q)) (z : ℂ) :
    S.compΛ (e :: P) z = S.ℓ e z + S.compΛ P (S.φ e z) := rfl

theorem mem_ball_of_mem_θ {a : Fin S.p} {z : ℂ}
    (hz : z ∈ closedBall (S.c a : ℂ) (S.θ * S.R a)) : z ∈ ball (S.c a : ℂ) (S.R a) :=
  S.closedBall_θ_subset_ball a hz

/-- **The chain rule**: `exp Λ_P = Φ_P′` on the open start disc. -/
theorem exp_compΛ {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : P ∈ S.paths a m) {z : ℂ}
    (hz : z ∈ ball (S.c a : ℂ) (S.R a)) :
    HasDerivAt (S.compφ P) (Complex.exp (S.compΛ P z)) z := by
  induction m generalizing a P z with
  | zero =>
    simp only [paths, Finset.mem_singleton] at hP
    subst hP
    simpa [compφ, compΛ] using hasDerivAt_id z
  | succ m ih =>
    obtain ⟨e, P', rfl, he, hP'⟩ := mem_paths_succ.mp hP
    subst he
    have hzd : z ∈ S.disc (S.src e) := ball_subset_closedBall hz
    have hφz : S.φ e z ∈ ball (S.c (S.tgt e) : ℂ) (S.R (S.tgt e)) :=
      S.mem_ball_of_mem_θ (S.φ_maps e hzd)
    have h1 : HasDerivAt (S.φ e) (Complex.exp (S.ℓ e z)) z := by
      rw [S.ℓ_exp e z hz]
      exact ((S.φ_diff e).differentiableAt
        (mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall)).hasDerivAt
    have h2 := ih hP' hφz
    have h3 := h2.comp z h1
    rw [compΛ_cons, Complex.exp_add, mul_comm]
    exact h3

/-- **Conjugation symmetry** of the composite and of its logarithmic derivative. -/
theorem compφ_conj {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : P ∈ S.paths a m) {z : ℂ}
    (hz : z ∈ S.disc a) :
    S.compφ P (conj z) = conj (S.compφ P z) ∧ S.compΛ P (conj z) = conj (S.compΛ P z) := by
  induction m generalizing a P z with
  | zero =>
    simp only [paths, Finset.mem_singleton] at hP
    subst hP
    simp [compφ, compΛ]
  | succ m ih =>
    obtain ⟨e, P', rfl, he, hP'⟩ := mem_paths_succ.mp hP
    subst he
    have hφz : S.φ e z ∈ S.disc (S.tgt e) :=
      closedBall_subset_closedBall (S.θ_mul_le _) (S.φ_maps e hz)
    obtain ⟨h1, h2⟩ := ih hP' hφz
    constructor <;>
      simp only [compφ_cons, compΛ_cons, S.φ_conj e z hz, S.ℓ_conj e z hz, h1, h2, map_add]

/-- A point of a disc with real centre has its conjugate in the disc. -/
theorem conj_mem_closedBall {x : ℝ} {r : ℝ} {z : ℂ} (hz : z ∈ closedBall (x : ℂ) r) :
    conj z ∈ closedBall (x : ℂ) r := by
  rw [mem_closedBall, dist_eq_norm] at hz ⊢
  rw [← Complex.conj_ofReal x, ← map_sub, Complex.norm_conj]
  exact hz

theorem conj_mem_ball {x : ℝ} {r : ℝ} {z : ℂ} (hz : z ∈ ball (x : ℂ) r) :
    conj z ∈ ball (x : ℂ) r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rw [← Complex.conj_ofReal x, ← map_sub, Complex.norm_conj]
  exact hz

/-- Along an admissible word, real points of a `θ`-subdisc have real `Λ` with `exp Λ ≤ κ^m`. -/
theorem compΛ_real_le {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : P ∈ S.paths a m)
    {x : ℝ} (hx : (x : ℂ) ∈ closedBall (S.c a : ℂ) (S.θ * S.R a)) :
    (S.compΛ P x).im = 0 ∧ Real.exp (S.compΛ P x).re ≤ S.κ ^ m := by
  induction m generalizing a P x with
  | zero =>
    simp only [paths, Finset.mem_singleton] at hP
    subst hP
    simp [compΛ]
  | succ m ih =>
    obtain ⟨e, P', rfl, he, hP'⟩ := mem_paths_succ.mp hP
    subst he
    have hxd : (x : ℂ) ∈ S.disc (S.src e) := closedBall_subset_closedBall (S.θ_mul_le _) hx
    -- `φ_e x` is real
    have hφreal : (S.φ e x).im = 0 := by
      have h := S.φ_conj e x hxd
      rw [Complex.conj_ofReal] at h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    have hℓreal : (S.ℓ e x).im = 0 := by
      have h := S.ℓ_conj e x hxd
      rw [Complex.conj_ofReal] at h
      have := congrArg Complex.im h
      rw [Complex.conj_im] at this
      linarith
    set y : ℝ := (S.φ e x).re with hy
    have hyx : S.φ e x = (y : ℂ) := Complex.ext (by simp [hy]) (by simp [hφreal])
    have hyθ : (y : ℂ) ∈ closedBall (S.c (S.tgt e) : ℂ) (S.θ * S.R (S.tgt e)) := by
      rw [← hyx]; exact S.φ_maps e hxd
    obtain ⟨ih1, ih2⟩ := ih hP' hyθ
    rw [compΛ_cons, hyx]
    refine ⟨by simp [hℓreal, ih1], ?_⟩
    rw [Complex.add_re, Real.exp_add, pow_succ']
    have hκ0 : 0 ≤ S.κ := (Real.exp_pos _).le.trans (S.expanding e x hx)
    exact mul_le_mul (S.expanding e x hx) ih2 (Real.exp_pos _).le hκ0

/-! ## Closed words and their fixed points -/

variable (S) in
/-- A closed admissible word of positive length. -/
def IsClosed (a : Fin S.p) (m : ℕ) (P : List (Fin S.q)) : Prop :=
  P ∈ S.paths a m ∧ S.endState a P = a ∧ m ≠ 0

theorem exists_fixPt {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : S.IsClosed a m P) :
    ∃ x, x ∈ closedBall (S.c a : ℂ) (S.θ * S.R a) ∧ S.compφ P x = x ∧
      (∀ y ∈ ball (S.c a : ℂ) (S.R a), S.compφ P y = y → y = x) ∧
      ‖deriv (S.compφ P) x‖ ≤ DiscFixedPoint.contractionFactor S.θ := by
  obtain ⟨hPm, hend, hm⟩ := hP
  have hd := (differentiableOn_compφ hPm).1
  have hmaps := (mapsTo_compφ hPm).2 hm
  rw [hend] at hmaps
  exact DiscFixedPoint.exists_unique_fixedPoint (S.R_pos a) S.θ_nonneg S.θ_lt_one
    (hd.mono ball_subset_closedBall) (hmaps.mono_left ball_subset_closedBall)

variable (S) in
open Classical in
/-- The fixed point of a closed word (the periodic point with this itinerary). -/
def fixPt (a : Fin S.p) (m : ℕ) (P : List (Fin S.q)) : ℂ :=
  if h : S.IsClosed a m P then Classical.choose (exists_fixPt h) else 0

theorem fixPt_spec {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : S.IsClosed a m P) :
    S.fixPt a m P ∈ closedBall (S.c a : ℂ) (S.θ * S.R a) ∧ S.compφ P (S.fixPt a m P) = S.fixPt a m P ∧
      (∀ y ∈ ball (S.c a : ℂ) (S.R a), S.compφ P y = y → y = S.fixPt a m P) ∧
      ‖deriv (S.compφ P) (S.fixPt a m P)‖ ≤ DiscFixedPoint.contractionFactor S.θ := by
  unfold fixPt
  rw [dif_pos hP]
  exact Classical.choose_spec (exists_fixPt hP)

/-- **The periodic point is real.** -/
theorem fixPt_real {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : S.IsClosed a m P) :
    (S.fixPt a m P).im = 0 := by
  obtain ⟨hmem, hfix, huniq, -⟩ := fixPt_spec hP
  set x := S.fixPt a m P
  have hxd : x ∈ S.disc a := closedBall_subset_closedBall (S.θ_mul_le a) hmem
  have hconj : S.compφ P (conj x) = conj x := by
    rw [(compφ_conj hP.1 hxd).1, hfix]
  have hcb : conj x ∈ ball (S.c a : ℂ) (S.R a) := conj_mem_ball (S.mem_ball_of_mem_θ hmem)
  have h := huniq (conj x) hcb hconj
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

variable (S) in
/-- The multiplier exponent `Λ_P = log (T^m)′⁻¹` at the periodic point. -/
def cycleΛ (a : Fin S.p) (m : ℕ) (P : List (Fin S.q)) : ℂ := S.compΛ P (S.fixPt a m P)

theorem cycleΛ_spec {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : S.IsClosed a m P) :
    (S.cycleΛ a m P).im = 0 ∧ Real.exp (S.cycleΛ a m P).re ≤ S.κ ^ m ∧
      deriv (S.compφ P) (S.fixPt a m P) = Complex.exp (S.cycleΛ a m P) := by
  obtain ⟨hmem, -, -, -⟩ := fixPt_spec hP
  have hreal := fixPt_real hP
  have hxr : S.fixPt a m P = (((S.fixPt a m P).re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hreal])
  have hmem' : (((S.fixPt a m P).re : ℝ) : ℂ) ∈ closedBall (S.c a : ℂ) (S.θ * S.R a) := by
    rw [← hxr]; exact hmem
  obtain ⟨h1, h2⟩ := compΛ_real_le hP.1 hmem'
  have h3 := (exp_compΛ hP.1 (S.mem_ball_of_mem_θ hmem')).deriv
  unfold cycleΛ
  rw [← hxr] at h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem norm_exp_cycleΛ_le {a : Fin S.p} {m : ℕ} {P : List (Fin S.q)} (hP : S.IsClosed a m P) :
    ‖Complex.exp (S.cycleΛ a m P)‖ ≤ DiscFixedPoint.contractionFactor S.θ := by
  rw [← (cycleΛ_spec hP).2.2]
  exact (fixPt_spec hP).2.2.2

end System

end GaloisForLFunctions.HTGeometry.AnalyticMarkov

end
