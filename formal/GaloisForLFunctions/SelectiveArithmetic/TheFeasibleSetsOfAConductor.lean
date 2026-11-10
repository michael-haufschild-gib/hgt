import GaloisForLFunctions.SelectiveArithmetic.TheLiouvilleTwistFailsBeyondTheTrivialAperture

/-!
# The feasible sets of a conductor

The feasible set of the conductor `q` at aperture `a` is the set of weight systems whose form,
with the counterterm of a comb of density `q` and no pole plane, is nonnegative on the tests
supported in `[−a, a]`.

* **Finite determinacy** (`contactForm_eq_of_floor_le`, `systemForm_eq_of_le`,
  `feasible_congr`): on a test supported in `[−a, a]` the form sees the weights `w(n)`,
  `n ≤ e^{2a}`, only, and does not change when the aperture of the form is enlarged.
* **Monotonicity** (`Feasible.anti`, `Feasible.mono_conductor`): the feasible sets decrease
  with the aperture and increase with the conductor.
* **Convexity** (`systemForm_add_smul`, `convex_feasible`): the form is affine in the weights.
* **A floor is a conductor** (`systemForm_conductor_mul_exp`, `feasible_mul_exp_iff`,
  `exists_not_floor`): the form with the conductor `q e^{K}` is the form with the conductor `q`
  plus `K ∫ |F|²`, so a uniform floor `−K ∫ |F|²` is feasibility at the conductor `q e^{K}`.
  Floors do not move the ladder: beyond the trivial aperture the Liouville twist violates every
  floor.
* **The trivial aperture is a threshold** (`bddAbove_feasibleApertures`,
  `feasible_of_lt_trivialAperture`, `exists_not_feasible_of_trivialAperture_lt`): for every
  conductor the apertures at which the whole dominated box is feasible are bounded; the box is
  feasible at every aperture below the trivial aperture, and above it some dominated system is
  infeasible.

With the pole plane of `ζ` in place of a conductor, nonemptiness of the feasible sets at every
aperture is the Riemann hypothesis (corpus). With a conductor the feasible sets are never empty
for a large conductor, and the question of the ladder is which systems stay feasible beyond the
trivial aperture.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ

/-! ### Finite determinacy -/

/-- On a test supported in `[−a, a]` the contacts beyond `e^{2a}` do not enter. -/
theorem contactForm_eq_of_floor_le {a : ℝ} {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Set.Icc (-a) a) (w : ℕ → ℝ) {N : ℕ}
    (hN : ⌊Real.exp (2 * a)⌋₊ ≤ N) :
    contactForm w F N = contactForm w F ⌊Real.exp (2 * a)⌋₊ := by
  obtain ⟨-, -, hks, -, -⟩ := _root_.RHTower.weilTest_self_data hF hFs
  have hout : ∀ y : ℝ, 2 * a < |y| → EF.weilTest F F y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun hmem => by
      have h := hks hmem
      have : |y| ≤ 2 * a := abs_le.mpr ⟨h.1, h.2⟩
      linarith
  unfold contactForm
  refine (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) fun n hn hn' => ?_).symm
  have hlt : ⌊Real.exp (2 * a)⌋₊ < n := by
    rw [Finset.mem_Icc] at hn hn'
    omega
  have hexp : Real.exp (2 * a) < n := (Nat.floor_lt (Real.exp_pos _).le).mp hlt
  have hlog : 2 * a < Real.log n := by
    rw [← Real.log_exp (2 * a)]
    exact Real.log_lt_log (Real.exp_pos _) hexp
  have hl0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [hout _ (by rwa [abs_of_nonneg hl0]), hout _ (by rwa [abs_neg, abs_of_nonneg hl0])]
  simp

/-- The form of a system on a test does not depend on the aperture at which it is taken. -/
theorem systemForm_eq_of_le {a b : ℝ} (hab : a ≤ b) {F : ℝ → ℂ} (hF : ContDiff ℝ 2 F)
    (hFs : tsupport F ⊆ Set.Icc (-a) a) (w : ℕ → ℝ) (q : ℝ) :
    systemForm w q b F = systemForm w q a F := by
  have hFs' : tsupport F ⊆ Set.Icc (-b) b :=
    hFs.trans (Set.Icc_subset_Icc (by linarith) hab)
  rw [systemForm_eq hF hFs', systemForm_eq hF hFs,
    contactForm_eq_of_floor_le hF hFs w
      (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith)))]

/-- The contact form depends on the weights `w(n)`, `2 ≤ n ≤ N`, only. -/
theorem contactForm_congr {w w' : ℕ → ℝ} {N : ℕ} (h : ∀ n, 2 ≤ n → n ≤ N → w n = w' n)
    (F : ℝ → ℂ) : contactForm w F N = contactForm w' F N := by
  unfold contactForm
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [h n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2]

/-- **Finite determinacy.** Feasibility at aperture `a` depends on the weights `w(n)`,
`n ≤ e^{2a}`, only. -/
theorem feasible_congr {q a : ℝ} {w w' : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → n ≤ ⌊Real.exp (2 * a)⌋₊ → w n = w' n) :
    Feasible q a w ↔ Feasible q a w' := by
  have key : ∀ {v v' : ℕ → ℝ}, (∀ n : ℕ, 2 ≤ n → n ≤ ⌊Real.exp (2 * a)⌋₊ → v n = v' n) →
      Feasible q a v → Feasible q a v' := by
    intro v v' hv hfe F hF hFs
    have h1 := hfe F hF hFs
    rw [systemForm_eq hF hFs] at h1 ⊢
    rwa [← contactForm_congr hv F]
  exact ⟨key h, key fun n hn hnN => (h n hn hnN).symm⟩

/-! ### Monotonicity -/

/-- The feasible sets decrease with the aperture. -/
theorem Feasible.anti {q a b : ℝ} {w : ℕ → ℝ} (h : Feasible q b w) (hab : a ≤ b) :
    Feasible q a w := fun F hF hFs => by
  rw [← systemForm_eq_of_le hab hF hFs]
  exact h F hF (hFs.trans (Set.Icc_subset_Icc (by linarith) hab))

/-- The feasible sets increase with the conductor. -/
theorem Feasible.mono_conductor {q q' a : ℝ} {w : ℕ → ℝ} (h : Feasible q a w)
    (hq : Real.log q ≤ Real.log q') : Feasible q' a w := fun F hF hFs => by
  have h1 := h F hF hFs
  have hmass : 0 ≤ ∫ x, ‖F x‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [systemForm_eq hF hFs] at h1 ⊢
  nlinarith [mul_le_mul_of_nonneg_right hq hmass]

/-! ### A floor is a conductor -/

/-- Enlarging the conductor by the factor `e^{K}` adds `K ∫ |F|²` to the form. -/
theorem systemForm_conductor_mul_exp {q : ℝ} (hq : 0 < q) (K : ℝ) {a : ℝ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) (w : ℕ → ℝ) :
    systemForm w (q * Real.exp K) a F = systemForm w q a F + K * ∫ x, ‖F x‖ ^ 2 := by
  rw [systemForm_eq hF hFs, systemForm_eq hF hFs,
    Real.log_mul hq.ne' (Real.exp_pos K).ne', Real.log_exp]
  ring

/-- **A uniform floor is feasibility at a larger conductor.** -/
theorem feasible_mul_exp_iff {q : ℝ} (hq : 0 < q) (K a : ℝ) (w : ℕ → ℝ) :
    Feasible (q * Real.exp K) a w ↔
      ∀ F : ℝ → ℂ, ContDiff ℝ 2 F → tsupport F ⊆ Set.Icc (-a) a →
        -(K * ∫ x, ‖F x‖ ^ 2) ≤ systemForm w q a F := by
  constructor
  · intro h F hF hFs
    have h1 := h F hF hFs
    rw [systemForm_conductor_mul_exp hq K hF hFs] at h1
    linarith
  · intro h F hF hFs
    rw [systemForm_conductor_mul_exp hq K hF hFs]
    linarith [h F hF hFs]

/-! ### Convexity -/

theorem contactForm_add_smul (s t : ℝ) (w₁ w₂ : ℕ → ℝ) (F : ℝ → ℂ) (N : ℕ) :
    contactForm (fun n => s * w₁ n + t * w₂ n) F N =
      s * contactForm w₁ F N + t * contactForm w₂ F N := by
  unfold contactForm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- The form of a system is affine in the weights. -/
theorem systemForm_add_smul {s t : ℝ} (hst : s + t = 1) {a : ℝ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) (w₁ w₂ : ℕ → ℝ) (q : ℝ) :
    systemForm (fun n => s * w₁ n + t * w₂ n) q a F =
      s * systemForm w₁ q a F + t * systemForm w₂ q a F := by
  rw [systemForm_eq hF hFs, systemForm_eq hF hFs, systemForm_eq hF hFs, contactForm_add_smul]
  linear_combination
    (-(1 / (2 * π) * (∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))) +
      Real.log q * ∫ x, ‖F x‖ ^ 2)) * hst

/-- **The feasible sets are convex.** -/
theorem convex_feasible (q a : ℝ) : Convex ℝ {w : ℕ → ℝ | Feasible q a w} := by
  intro w₁ h₁ w₂ h₂ s t hs ht hst
  show Feasible q a (s • w₁ + t • w₂)
  intro F hF hFs
  have e : (s • w₁ + t • w₂) = fun n => s * w₁ n + t * w₂ n := by
    funext n
    simp
  rw [e, systemForm_add_smul hst hF hFs]
  exact add_nonneg (mul_nonneg hs (h₁ F hF hFs)) (mul_nonneg ht (h₂ F hF hFs))

/-! ### The trivial aperture is a threshold -/

/-- For every conductor the apertures at which the whole dominated box is feasible are bounded:
beyond `log log q' + 1`, `log q' = max(M₀, log q)`, the Liouville twist is infeasible. -/
theorem bddAbove_feasibleApertures (q : ℝ) :
    BddAbove {a : ℝ | 0 ≤ a ∧ ∀ w : ℕ → ℝ, Dominated w → Feasible q a w} := by
  obtain ⟨M₀, -, hM₀⟩ := exists_not_feasible (η := 1) one_pos
  set L := max M₀ (Real.log q) with hL
  refine ⟨Real.log L + 1, fun a ha => ?_⟩
  by_contra hlt
  push Not at hlt
  have hlogq' : Real.log (Real.exp L) = L := Real.log_exp L
  have hfe : Feasible (Real.exp L) a liouvilleWeight :=
    (ha.2 _ dominated_liouvilleWeight).mono_conductor (by
      rw [hlogq']
      exact le_max_right _ _)
  refine (hM₀ (Real.exp L) (by rw [hlogq']; exact le_max_left _ _) a ?_).1 hfe
  rw [hlogq']
  exact hlt.le

/-- The trivial aperture is nonnegative. -/
theorem trivialAperture_nonneg (q : ℝ) : 0 ≤ trivialAperture q :=
  Real.sSup_nonneg fun _ ha => ha.1

/-- **Below the trivial aperture the dominated box is feasible.** -/
theorem feasible_of_lt_trivialAperture {q a : ℝ} (ha : a < trivialAperture q) {w : ℕ → ℝ}
    (hw : Dominated w) : Feasible q a w := by
  by_cases hne : {b : ℝ | 0 ≤ b ∧ ∀ v : ℕ → ℝ, Dominated v → Feasible q b v}.Nonempty
  · obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_csSup hne ha
    exact (hb.2 w hw).anti hab.le
  · -- an empty set of apertures has supremum `0`: every test supported in `[−a, a]`, `a < 0`,
    -- vanishes
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have h0 : trivialAperture q = 0 := by
      unfold trivialAperture
      rw [hne, Real.sSup_empty]
    rw [h0] at ha
    intro F hF hFs
    have hempty : Set.Icc (-a) a = ∅ := Set.Icc_eq_empty (by linarith)
    have hFz : F = 0 := by
      rw [← tsupport_eq_empty_iff]
      exact Set.subset_empty_iff.mp (hempty ▸ hFs)
    subst hFz
    simp [systemForm, paperFT]

/-- **Above the trivial aperture a dominated system is infeasible.** -/
theorem exists_not_feasible_of_trivialAperture_lt {q a : ℝ} (ha : trivialAperture q < a) :
    ∃ w : ℕ → ℝ, Dominated w ∧ ¬ Feasible q a w := by
  by_contra h
  push Not at h
  have ha0 : 0 ≤ a := (trivialAperture_nonneg q).trans ha.le
  have hmem : a ∈ {b : ℝ | 0 ≤ b ∧ ∀ v : ℕ → ℝ, Dominated v → Feasible q b v} := ⟨ha0, h⟩
  exact absurd (le_csSup (bddAbove_feasibleApertures q) hmem) (not_le.mpr ha)

/-- **Beyond the trivial aperture the Liouville twist violates every floor.** For every
`η > 0` and `K ≥ 0` and every conductor with `log q` large, at every aperture
`a ≥ log log q + η` some test supported in `[−a, a]` has
`𝔚_{λΛ,q}(F) < −K ∫ |F|²`. -/
theorem exists_not_floor {η K : ℝ} (hη : 0 < η) (hK : 0 ≤ K) :
    ∃ M₀ : ℝ, ∀ q : ℝ, 0 < q → M₀ ≤ Real.log q → ∀ a : ℝ, Real.log (Real.log q) + η ≤ a →
      ∃ F : ℝ → ℂ, ContDiff ℝ 2 F ∧ tsupport F ⊆ Set.Icc (-a) a ∧
        systemForm liouvilleWeight q a F < -(K * ∫ x, ‖F x‖ ^ 2) := by
  obtain ⟨M₁, hM₁1, hM₁⟩ := exists_not_feasible (half_pos hη)
  have hε : 0 < Real.exp (η / 2) - 1 := by
    have : Real.exp 0 < Real.exp (η / 2) := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  refine ⟨max M₁ (K / (Real.exp (η / 2) - 1)), fun q hq hqM a ha => ?_⟩
  have hx1 : M₁ ≤ Real.log q := (le_max_left _ _).trans hqM
  have hx0 : 0 < Real.log q := by linarith
  have hKx : K ≤ (Real.exp (η / 2) - 1) * Real.log q := by
    have h := (le_max_right _ _).trans hqM
    rwa [div_le_iff₀ hε] at h
  have hlogq' : Real.log (q * Real.exp K) = Real.log q + K := by
    rw [Real.log_mul hq.ne' (Real.exp_pos K).ne', Real.log_exp]
  -- the enlarged conductor has the same trivial aperture up to `η/2`
  have hll : Real.log (Real.log q + K) ≤ Real.log (Real.log q) + η / 2 := by
    have h1 : Real.log q + K ≤ Real.exp (η / 2) * Real.log q := by linarith
    calc Real.log (Real.log q + K) ≤ Real.log (Real.exp (η / 2) * Real.log q) :=
          Real.log_le_log (by linarith) h1
      _ = Real.log (Real.log q) + η / 2 := by
          rw [Real.log_mul (Real.exp_pos _).ne' hx0.ne', Real.log_exp]
          ring
  have hnot := (hM₁ (q * Real.exp K) (by rw [hlogq']; linarith) a (by
    rw [hlogq']
    linarith)).1
  rw [feasible_mul_exp_iff hq] at hnot
  push Not at hnot
  exact hnot

end GaloisForLFunctions.SelectiveArithmetic
