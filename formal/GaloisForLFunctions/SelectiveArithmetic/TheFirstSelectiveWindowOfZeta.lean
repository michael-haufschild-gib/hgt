import GaloisForLFunctions.SelectiveArithmetic.EveryVisibleWeightIsBoundedByTheMass

/-!
# The first selective window of `ζ`

With the pole plane of `ζ` in place of a conductor, a weight system `w` is feasible at aperture
`a` if Weil's functional with the contacts `w` is nonnegative on the autocorrelation of every
real packet supported in `[−a, a]`. Its form is the pole term plus the form of the system
`(w, 1)` (`re_weilFullFunctional_eq_pole_add_systemForm`).

* **Below the first contact** (`poleFeasible_iff_of_lt_half_log_two`): for `2a < log 2`
  feasibility does not depend on the weights; a window of ratio less than `2` is not selective.
* **At the first contact the weight at `2` is confined**
  (`exists_abs_weight_le_of_poleFeasible`): there is an absolute constant `C` such that every
  system feasible at an aperture `a ≥ ½ log n + r`, `0 < r ≤ 1/(4n)`, has
  `|w(n)| ≤ √n (log(1 + 1/r) + C)`. For `n = 2` and a window of ratio `2 e^{2r}` the feasible
  weights at `2` lie in an interval of half-length `√2 (log(1/r) + C)`. The pole term of a pair
  of narrow bumps is at most `12` times the mass of one bump.
* **The interval has an interior around `log 2`** (`poleFeasible_of_abs_sub_le`,
  `poleFeasible_vonMangoldt`): for `a ≤ 181/500` every system with
  `√2 |w(2) − log 2| ≤ 1/5000` is feasible; the margin of Weil's form on packets of width
  `181/250` (corpus) pays the change of the single visible weight.

So every window of ratio greater than `2` is selective for the weight at `2`: the feasible
interval is bounded, grows at most like `√2 log(1/r)` as the ratio decreases to `2`, and up to the
ratio `e^{181/250}` it contains a neighbourhood of `Λ(2) = log 2`. Its end points are numbers of a
finite computation; the structure is the logarithmic law at the contact.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ

/-! ### Feasibility with the pole plane -/

/-- A weight system is feasible with the pole plane of `ζ` at aperture `a` if Weil's functional
with the contacts `w` is nonnegative on every real packet supported in `[−a, a]`. -/
def PoleFeasible (a : ℝ) (w : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a →
    0 ≤ (_root_.RHTower.weilFullFunctional w
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re

/-- Weil's functional with contacts `w` is the pole term plus the form of the system `(w, 1)`. -/
theorem re_weilFullFunctional_eq_pole_add_systemForm (w : ℕ → ℝ) {a : ℝ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    (_root_.RHTower.weilFullFunctional w (EF.weilTest F F)).re =
      (_root_.RHTower.weilPoleTerm (EF.weilTest F F)).re + systemForm w 1 a F := by
  have e : systemForm w 1 a F =
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT F τ‖ ^ 2 *
        _root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
    unfold systemForm
    simp only [Real.log_one, add_zero]
  rw [re_weilFullFunctional_eq_pole_add_symbol w hF hFs, e]

theorem contactForm_sub (w w' : ℕ → ℝ) (F : ℝ → ℂ) (N : ℕ) :
    contactForm (fun n => w n - w' n) F N = contactForm w F N - contactForm w' F N := by
  unfold contactForm
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Changing the weights changes Weil's functional by the contact form of the difference. -/
theorem re_weilFullFunctional_eq_sub_contactForm (w w' : ℕ → ℝ) {a : ℝ} {F : ℝ → ℂ}
    (hF : ContDiff ℝ 2 F) (hFs : tsupport F ⊆ Set.Icc (-a) a) :
    (_root_.RHTower.weilFullFunctional w (EF.weilTest F F)).re =
      (_root_.RHTower.weilFullFunctional w' (EF.weilTest F F)).re -
        contactForm (fun n => w n - w' n) F ⌊Real.exp (2 * a)⌋₊ := by
  rw [re_weilFullFunctional_eq_pole_add_systemForm w hF hFs,
    re_weilFullFunctional_eq_pole_add_systemForm w' hF hFs, systemForm_eq hF hFs,
    systemForm_eq hF hFs, contactForm_sub]
  ring

/-- **Finite determinacy with the pole plane.** -/
theorem poleFeasible_congr {a : ℝ} {w w' : ℕ → ℝ}
    (h : ∀ n : ℕ, 2 ≤ n → n ≤ ⌊Real.exp (2 * a)⌋₊ → w n = w' n) :
    PoleFeasible a w ↔ PoleFeasible a w' := by
  have key : ∀ {v v' : ℕ → ℝ}, (∀ n : ℕ, 2 ≤ n → n ≤ ⌊Real.exp (2 * a)⌋₊ → v n = v' n) →
      PoleFeasible a v → PoleFeasible a v' := by
    intro v v' hv hfe f hf hfs
    have h0 : contactForm (fun n => v' n - v n) (fun u => (f u : ℂ)) ⌊Real.exp (2 * a)⌋₊ = 0 := by
      rw [contactForm_congr (w' := fun _ => 0) (fun n hn hnN => by rw [hv n hn hnN, sub_self])]
      simp [contactForm]
    rw [re_weilFullFunctional_eq_sub_contactForm v' v (contDiff_ofReal_packet hf) hfs, h0,
      sub_zero]
    exact hfe f hf hfs
  exact ⟨key h, key fun n hn hnN => (h n hn hnN).symm⟩

/-- **A window of ratio less than `2` is not selective.** For `2a < log 2` feasibility with the
pole plane does not depend on the weight system. -/
theorem poleFeasible_iff_of_lt_half_log_two {a : ℝ} (ha : 2 * a < Real.log 2) (w w' : ℕ → ℝ) :
    PoleFeasible a w ↔ PoleFeasible a w' := by
  refine poleFeasible_congr fun n hn hnN => ?_
  have h1 : (n : ℝ) ≤ Real.exp (2 * a) :=
    (Nat.cast_le.mpr hnN).trans (Nat.floor_le (Real.exp_pos _).le)
  have h2 : Real.exp (2 * a) < 2 := by
    calc Real.exp (2 * a) < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr ha
      _ = 2 := Real.exp_log two_pos
  have h3 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-! ### The feasible interval has an interior around `log 2` -/

/-- A packet with topological support in `[−a, a]` vanishes off `[−a, a]`. -/
theorem eq_zero_of_abs_gt_of_tsupport {f : ℝ → ℝ} {a : ℝ}
    (hfs : tsupport (fun u => (f u : ℂ)) ⊆ Set.Icc (-a) a) {u : ℝ} (hu : a < |u|) : f u = 0 := by
  have hnot : u ∉ tsupport fun u => (f u : ℂ) := fun hmem => by
    have h := hfs hmem
    have : |u| ≤ a := abs_le.mpr ⟨h.1, h.2⟩
    linarith
  have h0 : ((f u : ℝ) : ℂ) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun u => ((f u : ℝ) : ℂ)) hnot
  exact_mod_cast h0

/-- For `a ≤ 181/500` only the contact `2` is visible. -/
theorem floor_exp_le_two {a : ℝ} (ha : a ≤ 181 / 500) : ⌊Real.exp (2 * a)⌋₊ ≤ 2 := by
  have hlog3 : (181 : ℝ) / 250 < Real.log 3 := by
    have h1 := Real.log_two_gt_d9
    have h2 : (1 : ℝ) - (3 / 2 : ℝ)⁻¹ ≤ Real.log (3 / 2) :=
      Real.one_sub_inv_le_log_of_pos (by norm_num)
    have h3 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    rw [h3]
    norm_num at h2
    linarith
  have hlt : Real.exp (2 * a) < ((3 : ℕ) : ℝ) := by
    calc Real.exp (2 * a) < Real.exp (Real.log 3) := Real.exp_lt_exp.mpr (by linarith)
      _ = ((3 : ℕ) : ℝ) := by rw [Real.exp_log (by norm_num)]; norm_num
  exact Nat.lt_succ_iff.mp ((Nat.floor_lt (Real.exp_pos _).le).mpr hlt)

/-- **The feasible interval of the first contact contains a neighbourhood of `log 2`.** For
`a ≤ 181/500` every weight system with `√2 |w(2) − log 2| ≤ 1/5000` is feasible with the pole
plane. -/
theorem poleFeasible_of_abs_sub_le {a : ℝ} (ha : a ≤ 181 / 500) {w : ℕ → ℝ}
    (hw : Real.sqrt 2 * |w 2 - Real.log 2| ≤ 1 / 5000) : PoleFeasible a w := by
  intro f hf hfs
  have hF := contDiff_ofReal_packet hf
  have hFc : HasCompactSupport fun u => (f u : ℂ) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hfs
  have hf0 : ∀ u, a < |u| → f u = 0 := fun u hu => eq_zero_of_abs_gt_of_tsupport hfs hu
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => hf0 u (by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h))
  -- the margin of Weil's form on packets of width `181/250`
  have hΛ := zeroSum_ge_of_width hf hfc (c := 0) fun u hu =>
    hf0 u (by rw [sub_zero] at hu; linarith)
  rw [zeroSum_eq_weilFullFunctional hf hfc] at hΛ
  -- the single visible weight
  have hc := (abs_le.mp (abs_contactForm_le_sum_abs hF hFc (fun n => w n - Λ n)
    ⌊Real.exp (2 * a)⌋₊)).2
  have hΛ2 : (Λ 2 : ℝ) = Real.log 2 := by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr two_pos
  have hsum : ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * |w n - Λ n| / Real.sqrt n ≤
      Real.sqrt 2 * |w 2 - Real.log 2| := by
    have hsub : Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊ ⊆ ({2} : Finset ℕ) := fun n hn => by
      have := floor_exp_le_two ha
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_singleton]
      omega
    calc ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊, 2 * |w n - Λ n| / Real.sqrt n
        ≤ ∑ n ∈ ({2} : Finset ℕ), 2 * |w n - Λ n| / Real.sqrt n :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
      _ = Real.sqrt 2 * |w 2 - Real.log 2| := by
          rw [Finset.sum_singleton, hΛ2]
          have e : (2 : ℝ) = Real.sqrt 2 * Real.sqrt 2 := (Real.mul_self_sqrt (by norm_num)).symm
          push_cast
          field_simp
          nlinarith [abs_nonneg (w 2 - Real.log 2)]
  have hmass : 0 ≤ ∫ x, ‖((f x : ℝ) : ℂ)‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  rw [integral_norm_ofReal_sq] at hc hmass
  rw [re_weilFullFunctional_eq_sub_contactForm w (fun n => Λ n) hF hfs]
  nlinarith [mul_le_mul_of_nonneg_right (hsum.trans hw) hmass]

/-- Weil's form of `ζ` is nonnegative on packets of aperture at most `181/500` (corpus), in the
language of feasibility. -/
theorem poleFeasible_vonMangoldt {a : ℝ} (ha : a ≤ 181 / 500) :
    PoleFeasible a fun n => Λ n :=
  poleFeasible_of_abs_sub_le ha (by
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num)

/-! ### The weight at a contact is confined -/

/-- **The pole term of a pair of narrow bumps** at distance `log n`, `r ≤ 1/(4n)`, is at most
`12` times the mass of one bump. -/
theorem abs_re_weilPoleTerm_twoBump_le {s r : ℝ} (hs : s * s = 1) (hr : 0 < r) {n : ℕ}
    (hn : 2 ≤ n) (hrn : r ≤ 1 / (4 * (n : ℝ))) :
    |(_root_.RHTower.weilPoleTerm (EF.weilTest
        (fun u => (twoBump s (Real.log n / 2) r u : ℂ))
        (fun u => (twoBump s (Real.log n / 2) r u : ℂ)))).re| ≤
      12 * packetAutocorr (cutoff r (r / 2)) 0 := by
  have hδ : 0 < r / 2 := by positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr8 : r ≤ 1 / 8 := by
    refine hrn.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = Real.log n / 2 := ⟨_, rfl⟩
  rw [← hh]
  have hh0 : 0 ≤ h := by
    rw [hh]
    have := Real.log_nonneg hn1
    linarith
  obtain ⟨b, hb⟩ : ∃ b : ℝ → ℝ, b = cutoff r (r / 2) := ⟨_, rfl⟩
  have hbc : Continuous b := by rw [hb]; exact (contDiff_cutoff r (r / 2)).continuous
  have hb0 : ∀ u, 0 ≤ b u := fun u => by rw [hb]; exact cutoff_nonneg _ _ _
  have hbz : ∀ u, r < |u| → b u = 0 := fun u hu => by
    rw [hb]
    exact cutoff_eq_zero hδ hu.le
  have hbcs : HasCompactSupport b := by rw [hb]; exact hasCompactSupport_cutoff hδ
  have hbI : Integrable b := hbc.integrable_of_hasCompactSupport hbcs
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ∫ u, b u := ⟨_, rfl⟩
  have hm0 : 0 ≤ m := by rw [hm]; exact integral_nonneg hb0
  obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ₀ : ℝ, Φ₀ = packetAutocorr (cutoff r (r / 2)) 0 := ⟨_, rfl⟩
  rw [← hΦ₀]
  -- `m² ≤ 2r Φ₀`
  have hmsq : m ^ 2 ≤ 2 * r * Φ₀ := by
    have h1 := sq_integral_abs_le hbc hr.le hbz
    have e1 : ∫ u, |b u| = m := by
      rw [hm]
      exact integral_congr_ae (Eventually.of_forall fun u => abs_of_nonneg (hb0 u))
    have e2 : ∫ u, b u ^ 2 = Φ₀ := by
      rw [hΦ₀, packetAutocorr, ← hb]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show b u ^ 2 = b u * b (u + 0)
      rw [add_zero, sq]
    rwa [e1, e2] at h1
  -- the test and its two polar transforms
  obtain ⟨f, hf⟩ : ∃ f : ℝ → ℝ, f = twoBump s h r := ⟨_, rfl⟩
  rw [← hf]
  have hfC : ContDiff ℝ 3 f := by rw [hf]; exact contDiff_twoBump s h r
  have hfz : ∀ u, h + r ≤ |u| → f u = 0 := fun u hu => by
    rw [hf]
    exact twoBump_eq_zero hr hh0 le_rfl hu
  have hFcont : Continuous fun u => (f u : ℂ) := Complex.continuous_ofReal.comp hfC.continuous
  have hFc : HasCompactSupport fun u => (f u : ℂ) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (tsupport_ofReal_subset_of_eq_zero hfz)
  have hs1 : |s| = 1 := by
    have h1 : |s| * |s| = 1 := by rw [← abs_mul, hs, abs_one]
    nlinarith [abs_nonneg s]
  have hi1 : Integrable fun u => b (u + h) := hbI.comp_add_right h
  have hi2 : Integrable fun u => b (u - h) := hbI.comp_sub_right h
  have hJ : ∫ u, ‖((f u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) ≤
      Real.exp ((h + r) / 2) * (2 * m) := by
    have hrhs : ∫ u, Real.exp ((h + r) / 2) * (b (u + h) + b (u - h)) =
        Real.exp ((h + r) / 2) * (2 * m) := by
      rw [integral_const_mul, integral_add hi1 hi2,
        integral_add_right_eq_self (fun u => b u) h,
        integral_sub_right_eq_self (fun u => b u) h, ← hm]
      ring
    rw [← hrhs]
    refine integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity)
      ((hi1.add hi2).const_mul _) (Eventually.of_forall fun u => ?_)
    show ‖((f u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|) ≤
      Real.exp ((h + r) / 2) * (b (u + h) + b (u - h))
    have hsum0 : 0 ≤ b (u + h) + b (u - h) := add_nonneg (hb0 _) (hb0 _)
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hu : h + r ≤ |u|
    · rw [hfz u hu, abs_zero, zero_mul]
      exact mul_nonneg (Real.exp_pos _).le hsum0
    · push Not at hu
      have hfu : |f u| ≤ b (u + h) + b (u - h) := by
        rw [hf, twoBump, ← hb]
        calc |b (u + h) + s * b (u - h)| ≤ |b (u + h)| + |s * b (u - h)| := abs_add_le _ _
          _ = b (u + h) + b (u - h) := by
              rw [abs_of_nonneg (hb0 _), abs_mul, hs1, one_mul, abs_of_nonneg (hb0 _)]
      have hexp : Real.exp (1 / 2 * |u|) ≤ Real.exp ((h + r) / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      calc |f u| * Real.exp (1 / 2 * |u|)
          ≤ (b (u + h) + b (u - h)) * Real.exp ((h + r) / 2) :=
            mul_le_mul hfu hexp (Real.exp_pos _).le hsum0
        _ = Real.exp ((h + r) / 2) * (b (u + h) + b (u - h)) := mul_comm _ _
  have hA := (_root_.RHTower.EvenSector.norm_paperFT_le_of_compact hFcont hFc (b := 1 / 2)
    (z := Complex.I / 2) (by simp)).trans hJ
  have hB := (_root_.RHTower.EvenSector.norm_paperFT_le_of_compact hFcont hFc (b := 1 / 2)
    (z := -Complex.I / 2) (by
      simp
      rw [abs_le]
      constructor <;> norm_num)).trans hJ
  obtain ⟨A, hAdef⟩ : ∃ A : ℂ, A = paperFT (fun u => (f u : ℂ)) (Complex.I / 2) := ⟨_, rfl⟩
  obtain ⟨Bc, hBdef⟩ : ∃ Bc : ℂ, Bc = paperFT (fun u => (f u : ℂ)) (-Complex.I / 2) := ⟨_, rfl⟩
  rw [← hAdef] at hA
  rw [← hBdef] at hB
  -- `e^{h + r} ≤ 3 √n` and `r √n ≤ 1/4`
  have hexpsq : Real.exp ((h + r) / 2) * Real.exp ((h + r) / 2) = Real.exp (h + r) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hexph : Real.exp h = Real.sqrt n := by
    have e := BiScaleUncertainty.exp_add_half_log (by omega : 0 < n) 0
    rw [zero_add, Real.exp_zero, one_mul] at e
    rw [hh]
    exact e
  have hexpr : Real.exp r ≤ 3 := by
    have h1 : Real.exp r ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
    linarith [Real.exp_one_lt_d9]
  have hrsn : r * Real.sqrt n ≤ 1 / 4 := by
    have hsle : Real.sqrt n ≤ n := by
      have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
      have h1 : 1 ≤ Real.sqrt n := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
      nlinarith
    have h1 : r * (n : ℝ) ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_right hrn hn0.le
      have e : 1 / (4 * (n : ℝ)) * n = 1 / 4 := by field_simp
      linarith
    nlinarith
  have hAB : ‖A‖ * ‖Bc‖ ≤ 6 * Φ₀ := by
    have h1 : ‖A‖ * ‖Bc‖ ≤
        Real.exp ((h + r) / 2) * (2 * m) * (Real.exp ((h + r) / 2) * (2 * m)) :=
      mul_le_mul hA hB (norm_nonneg _) (by positivity)
    have e : Real.exp ((h + r) / 2) * (2 * m) * (Real.exp ((h + r) / 2) * (2 * m)) =
        Real.exp (h + r) * (4 * m ^ 2) := by
      rw [← hexpsq]
      ring
    rw [e, Real.exp_add, hexph] at h1
    have hΦnn : 0 ≤ Φ₀ := by
      have := le_packetAutocorr_cutoff_zero hr
      rw [← hΦ₀] at this
      linarith
    have h2 : Real.sqrt n * Real.exp r * (4 * m ^ 2) ≤
        Real.sqrt n * 3 * (4 * (2 * r * Φ₀)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hexpr hsn.le)
        (mul_le_mul_of_nonneg_left hmsq (by norm_num)) (by positivity) (by positivity)
    have h3 : Real.sqrt n * 3 * (4 * (2 * r * Φ₀)) = 24 * (r * Real.sqrt n) * Φ₀ := by ring
    have h4 : 24 * (r * Real.sqrt n) * Φ₀ ≤ 24 * (1 / 4) * Φ₀ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrsn (by norm_num)) hΦnn
    linarith
  rw [_root_.RHTower.WeilOneSided.weilPoleTerm_re_eq_two_re hFcont hFc, ← hAdef, ← hBdef]
  have hre : |(A * conj Bc).re| ≤ ‖A‖ * ‖Bc‖ := by
    have h := Complex.abs_re_le_norm (A * conj Bc)
    rwa [norm_mul, Complex.norm_conj] at h
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- **The box law with the pole plane.** There is an absolute constant `C` such that every
system feasible with the pole plane of `ζ` at aperture `a` satisfies
`|w(n)| ≤ √n (log(1 + 1/r) + C)` at every `n ≥ 2` and every `0 < r ≤ 1/(4n)` with
`½ log n + r ≤ a`. -/
theorem exists_abs_weight_le_of_poleFeasible :
    ∃ C : ℝ, ∀ {a r : ℝ} {w : ℕ → ℝ} {n : ℕ}, 2 ≤ n → 0 < r → r ≤ 1 / (4 * (n : ℝ)) →
      Real.log n / 2 + r ≤ a → PoleFeasible a w →
      |w n| ≤ Real.sqrt n * (Real.log (1 + 1 / r) + C) := by
  obtain ⟨S, -, hS⟩ := exists_abs_deriv_smoothTransition_le
  refine ⟨11 + 64 * S ^ 2, fun {a r w n} hn hr0 hrn ha hfe => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hr8 : r ≤ 1 / 8 := by
    refine hrn.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hh0 : 0 ≤ Real.log n / 2 := by linarith
  have hrh : r ≤ Real.log n / 2 := by linarith
  obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ₀ : ℝ, Φ₀ = packetAutocorr (cutoff r (r / 2)) 0 := ⟨_, rfl⟩
  have hΦpos : 0 < Φ₀ := by
    rw [hΦ₀]
    exact lt_of_lt_of_le hr0 (le_packetAutocorr_cutoff_zero hr0)
  have hnN : n ≤ ⌊Real.exp (2 * a)⌋₊ := by
    refine Nat.le_floor ?_
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
      _ ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by linarith)
  have key : ∀ s : ℝ, s * s = 1 →
      s * w n ≤ Real.sqrt n * (Real.log (1 + 1 / r) + (11 + 64 * S ^ 2)) := by
    intro s hs
    have hf := contDiff_twoBump s (Real.log n / 2) r
    have h0 : ∀ u, a ≤ |u| → twoBump s (Real.log n / 2) r u = 0 := fun u hu =>
      twoBump_eq_zero hr0 hh0 ha hu
    have hF := contDiff_ofReal_packet (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
    have hFs := tsupport_ofReal_subset_of_eq_zero h0
    have hpos := hfe _ (hf.of_le (by norm_num)) hFs
    rw [re_weilFullFunctional_eq_pole_add_systemForm w hF hFs] at hpos
    have hpole := (abs_le.mp (abs_re_weilPoleTerm_twoBump_le hs hr0 hn hrn)).2
    have hup := systemForm_le_of_packet_scaled hr0 hf h0 w 1
    have hD := sq_mul_integral_deriv_twoBump_sq_le hS hs (Real.log n / 2) hr0
    rw [contactForm_twoBump hs hr0 hn hrn w hnN, integral_twoBump_sq hs hr0 hrh, ← hΦ₀,
      Real.log_one, add_zero] at hup
    rw [← hΦ₀] at hD hpole
    have hfin : w n / Real.sqrt n * (2 * (s * Φ₀)) ≤
        (2 * (Real.log (1 + 1 / r) + 5) + 128 * S ^ 2 + 12) * Φ₀ := by
      linarith
    have hdiv : s * w n / Real.sqrt n ≤ Real.log (1 + 1 / r) + 11 + 64 * S ^ 2 := by
      have e : w n / Real.sqrt n * (2 * (s * Φ₀)) = (2 * (s * w n / Real.sqrt n)) * Φ₀ := by
        ring
      rw [e] at hfin
      have := le_of_mul_le_mul_right hfin hΦpos
      linarith
    rw [div_le_iff₀ hsn] at hdiv
    linarith
  have hp := key 1 (by norm_num)
  have hm := key (-1) (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end GaloisForLFunctions.SelectiveArithmetic
