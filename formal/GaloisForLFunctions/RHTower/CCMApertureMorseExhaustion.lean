import GaloisForLFunctions.RHTower.CCMTwoChannelGraph
import GaloisForLFunctions.RHTower.CCMApertureMorseCharge
import GaloisForLFunctions.HTGeometry.PerturbedNegativeDefinite

/-!
# The aperture Morse charge exhausts the Hardy off-line model-space index

Suzuki's global screw kernel is assembled from the features `phi_gamma (t) = (e^{i gamma t}-1)/gamma`
of `(7)`.  A real ordinate contributes the *positive* rank-one packet `(8)`; a nonreal conjugate
pair contributes `phi_gamma ⊗ phi_gammabar^* + phi_gammabar ⊗ phi_gamma^*`, which polarizes as `(9)`
into one positive minus one **negative** square.  Every feature vanishes at the base point, so the
zero-mean row and column of `(12)` are zero and the projection costs no negative charge.

The exhaustion `(11)` uses exactly two mechanisms, both proved here.  Its *lower bound* needs the
stability of a strictly negative-definite subspace under a perturbation smaller than its coercivity
margin — the bump replacement of point masses — which upgrades to a lower bound on the Morse charge
of `RHTower/CCMApertureMorseCharge.lean`.  The *congruence* `(15)`–`(16)` needs that a linear
equivalence transports negative-definite subspaces with their dimension, so the derivative map `(14)`
loses no index.  Finally the two-sided squeeze of `(4)` and the cofinal shift of `(17)` are recorded:
a supremum pinned by an upper bound and a cofinal family of witnesses, and the fact that any finite
packet of right-half zeros has a *uniform* positive horizontal displacement.

The analytic screw series `(6)`, the Krein–Langer pole/index theorem `(10)` and the Hardy
model-space dimension `(3)` are cited parents and stay outside the Lean statement.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The screw features and their packets -/

/-- The screw feature `(7)`, `phi_gamma (t) = (e^{i gamma t} - 1)/gamma`. -/
def screwFeature (γ : ℂ) (t : ℝ) : ℂ := (Complex.exp (Complex.I * γ * (t : ℂ)) - 1) / γ

/-- **Equation (12).**  Every screw feature vanishes at the base point. -/
theorem screwFeature_zero (γ : ℂ) : screwFeature γ 0 = 0 := by
  unfold screwFeature
  simp

/-- The rank-one packet `(8)` of a single ordinate. -/
def screwPacket (γ : ℂ) (t u : ℝ) : ℂ := screwFeature γ t * (starRingEnd ℂ) (screwFeature γ u)

/-- **Equation (12), row.**  The base-point row of every packet vanishes. -/
theorem screwPacket_zero_left (γ : ℂ) (u : ℝ) : screwPacket γ 0 u = 0 := by
  unfold screwPacket
  rw [screwFeature_zero, zero_mul]

/-- **Equation (12), column.**  The base-point column of every packet vanishes. -/
theorem screwPacket_zero_right (γ : ℂ) (t : ℝ) : screwPacket γ t 0 = 0 := by
  unfold screwPacket
  rw [screwFeature_zero, map_zero, mul_zero]

/-- The generic rank-one kernel of a feature vector. -/
theorem rankOne_quadratic_eq {n : ℕ} (f : Fin n → ℂ) (c : Fin n → ℂ) :
    (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (f i * (starRingEnd ℂ) (f j)))
      = (∑ i, c i * f i) * (starRingEnd ℂ) (∑ j, c j * f j) := by
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

/-- **Equation (8).**  A real ordinate contributes a *positive* rank-one packet: its Gram quadratic
form is a squared modulus. -/
theorem screwPacket_quadratic_nonneg {n : ℕ} (γ : ℂ) (t : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * screwPacket γ (t i) (t j)).re := by
  have hfac := rankOne_quadratic_eq (fun i => screwFeature γ (t i)) c
  rw [show (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * screwPacket γ (t i) (t j))
      = ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j)
        * (screwFeature γ (t i) * (starRingEnd ℂ) (screwFeature γ (t j))) from rfl,
    hfac, Complex.mul_conj]
  rw [Complex.ofReal_re]
  exact Complex.normSq_nonneg _

/-! ## The conjugate pair carries one negative square -/

/-- **Equation (9).**  The conjugate-pair packet polarizes into one positive square minus one
negative square, at the level of the kernel itself. -/
theorem conjugate_pair_polarization (γ : ℂ) (t u : ℝ) :
    screwFeature γ t * (starRingEnd ℂ) (screwFeature ((starRingEnd ℂ) γ) u)
        + screwFeature ((starRingEnd ℂ) γ) t * (starRingEnd ℂ) (screwFeature γ u)
      = (1 / 2) * ((screwFeature γ t + screwFeature ((starRingEnd ℂ) γ) t)
            * (starRingEnd ℂ) (screwFeature γ u + screwFeature ((starRingEnd ℂ) γ) u))
        - (1 / 2) * ((screwFeature γ t - screwFeature ((starRingEnd ℂ) γ) t)
            * (starRingEnd ℂ) (screwFeature γ u - screwFeature ((starRingEnd ℂ) γ) u)) := by
  rw [map_add, map_sub]
  ring

/-- **Equation (9), quadratic form.**  The conjugate-pair contribution to any finite Gram form is
the difference of two squared moduli — the *one negative square* of the pair. -/
theorem conjugate_pair_quadratic_eq {n : ℕ} (γ : ℂ) (t : Fin n → ℝ) (c : Fin n → ℂ) :
    (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j)
        * (screwFeature γ (t i) * (starRingEnd ℂ) (screwFeature ((starRingEnd ℂ) γ) (t j))
          + screwFeature ((starRingEnd ℂ) γ) (t i) * (starRingEnd ℂ) (screwFeature γ (t j))))
      = (1 / 2) * ‖∑ i, c i * (screwFeature γ (t i) + screwFeature ((starRingEnd ℂ) γ) (t i))‖ ^ (2 : ℕ)
        - (1 / 2)
          * ‖∑ i, c i * (screwFeature γ (t i) - screwFeature ((starRingEnd ℂ) γ) (t i))‖ ^ (2 : ℕ) := by
  have hsplit : ∀ i j, c i * (starRingEnd ℂ) (c j)
      * (screwFeature γ (t i) * (starRingEnd ℂ) (screwFeature ((starRingEnd ℂ) γ) (t j))
        + screwFeature ((starRingEnd ℂ) γ) (t i) * (starRingEnd ℂ) (screwFeature γ (t j)))
      = (1 / 2) * (c i * (starRingEnd ℂ) (c j)
            * ((screwFeature γ (t i) + screwFeature ((starRingEnd ℂ) γ) (t i))
              * (starRingEnd ℂ) (screwFeature γ (t j) + screwFeature ((starRingEnd ℂ) γ) (t j))))
        - (1 / 2) * (c i * (starRingEnd ℂ) (c j)
            * ((screwFeature γ (t i) - screwFeature ((starRingEnd ℂ) γ) (t i))
              * (starRingEnd ℂ) (screwFeature γ (t j) - screwFeature ((starRingEnd ℂ) γ) (t j)))) := by
    intro i j
    rw [map_add, map_sub]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hsplit i j]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [rankOne_quadratic_eq (fun i => screwFeature γ (t i) + screwFeature ((starRingEnd ℂ) γ) (t i)),
    rankOne_quadratic_eq (fun i => screwFeature γ (t i) - screwFeature ((starRingEnd ℂ) γ) (t i)),
    Complex.mul_conj, Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-! ## Exhaustion: the lower bound -/

/-- **Section 2, lower bound.**  A negative-definite subspace of the limiting form survives every
perturbation smaller than its coercivity margin, with the same dimension.  This is the bump
replacement of the point Gram matrix. -/
theorem hasNegDefSubspaceOfDim_of_perturbation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Q Q₀ : E → ℝ) {δ ε : ℝ} (hε : ε < δ)
    (h₀ : ∀ x, Q₀ x ≤ -δ * ‖x‖ ^ (2 : ℕ))
    (hpert : ∀ x, |Q x - Q₀ x| ≤ ε * ‖x‖ ^ (2 : ℕ))
    {D W : Submodule ℝ E} (hWD : W ≤ D) {k : ℕ} (hdim : Module.finrank ℝ W = k) :
    HasNegDefSubspaceOfDim Q D k :=
  ⟨W, hWD, hdim, fun v _ hv =>
    GaloisForLFunctions.HTGeometry.neg_of_perturbed_negDef Q Q₀ hε h₀ hpert v hv⟩

/-- **Equation (5).**  The Morse charge of the perturbed aperture form is at least the negative
inertia `k` of the limiting point Gram matrix. -/
theorem le_morseCharge_of_perturbation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q Q₀ : E → ℝ) {δ ε : ℝ} (hε : ε < δ)
    (h₀ : ∀ x, Q₀ x ≤ -δ * ‖x‖ ^ (2 : ℕ))
    (hpert : ∀ x, |Q x - Q₀ x| ≤ ε * ‖x‖ ^ (2 : ℕ))
    {D W : Submodule ℝ E} (hWD : W ≤ D) {k : ℕ} (hdim : Module.finrank ℝ W = k)
    (hbdd : BddAbove {n : ℕ | HasNegDefSubspaceOfDim Q D n}) :
    k ≤ morseCharge Q D :=
  le_csSup hbdd (hasNegDefSubspaceOfDim_of_perturbation Q Q₀ hε h₀ hpert hWD hdim)

/-! ## The derivative congruence transports the index -/

/-- **Equations (14)–(16).**  A linear equivalence transports negative-definite subspaces with their
dimension: Suzuki's bijective derivative map loses no negative index. -/
theorem hasNegDefSubspaceOfDim_map {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (D : V ≃ₗ[ℝ] W) (G : W → ℝ) {Dom : Submodule ℝ V} {k : ℕ}
    (h : HasNegDefSubspaceOfDim (fun v => G (D v)) Dom k) :
    HasNegDefSubspaceOfDim G (Dom.map (D : V →ₗ[ℝ] W)) k := by
  obtain ⟨U, hUD, hdim, hneg⟩ := h
  refine ⟨U.map (D : V →ₗ[ℝ] W), Submodule.map_mono hUD, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq D U]
    exact hdim
  · rintro w ⟨v, hvU, rfl⟩ hwne
    refine hneg v hvU ?_
    intro hv0
    exact hwne (by rw [hv0]; simp)

/-- **Equation (16), reverse transport.**  The pullback of a negative-definite subspace along the
equivalence is one for the pulled-back form. -/
theorem hasNegDefSubspaceOfDim_comap {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (D : V ≃ₗ[ℝ] W) (G : W → ℝ) {Dom : Submodule ℝ W} {k : ℕ}
    (h : HasNegDefSubspaceOfDim G Dom k) :
    HasNegDefSubspaceOfDim (fun v => G (D v)) (Dom.map (D.symm : W →ₗ[ℝ] V)) k := by
  obtain ⟨U, hUD, hdim, hneg⟩ := h
  refine ⟨U.map (D.symm : W →ₗ[ℝ] V), Submodule.map_mono hUD, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq D.symm U]
    exact hdim
  · rintro v ⟨w, hwU, rfl⟩ hvne
    have hDv : D ((D.symm : W →ₗ[ℝ] V) w) = w := by simp
    show G (D ((D.symm : W →ₗ[ℝ] V) w)) < 0
    rw [hDv]
    refine hneg w hwU ?_
    intro hw0
    exact hvne (by rw [hw0]; simp)

/-! ## The two-sided squeeze -/

/-- **Equation (4), squeeze.**  A set of achievable negative dimensions bounded by `N` and reaching
every value up to `N` has supremum exactly `N`. -/
theorem sSup_eq_of_le_of_cofinal {S : Set ℕ} {N : ℕ}
    (hle : ∀ n ∈ S, n ≤ N) (hex : ∀ k ≤ N, ∃ n ∈ S, k ≤ n) : sSup S = N := by
  obtain ⟨n₀, hn₀S, hn₀⟩ := hex N le_rfl
  refine le_antisymm (csSup_le ⟨n₀, hn₀S⟩ hle) ?_
  exact le_trans hn₀ (le_csSup ⟨N, hle⟩ hn₀S)

/-- **Equation (10), infinite case.**  If negative dimensions of every size occur, the achievable
set is unbounded: an infinite pole count is an infinite index. -/
theorem not_bddAbove_of_cofinal {S : Set ℕ} (hex : ∀ k : ℕ, ∃ n ∈ S, k ≤ n) :
    ¬ BddAbove S := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hnS, hn⟩ := hex (M + 1)
  exact absurd (le_trans hn (hM hnS)) (by omega)

/-! ## Cofinal exhaustion of the horizontal shift -/

/-- **Equation (17).**  Every finite packet of right-half zeros has a *uniform* positive horizontal
displacement, so the monotone family of shifted denominators exhausts the packet. -/
theorem exists_uniform_shift {S : Finset ℂ} (hS : ∀ ρ ∈ S, 1 / 2 < ρ.re) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ ρ ∈ S, 1 / 2 + ω < ρ.re := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨ρ₀, hρ₀S, hρ₀⟩ :=
      S.exists_min_image (fun ρ => ρ.re) hne
    refine ⟨(ρ₀.re - 1 / 2) / 2, by have := hS ρ₀ hρ₀S; linarith, fun ρ hρ => ?_⟩
    have h1 := hρ₀ ρ hρ
    have h2 := hS ρ₀ hρ₀S
    linarith

end GaloisForLFunctions.RHTower

end
