/-
The conservation ledger, assembled: anchored even-flux deformation chains force the
multiplicity-divisibility rungs.

A ledger chain on the slit annulus charts of `(a, r₀, R)` is a finite sequence of moves,
each either a dominated perturbation (`‖next − current‖ < ‖current‖` on the charts — no
zero touches the annulus) or a transversal jump (the enclosed configuration gains or loses
one zero of multiplicity `m` inside the hole).  Transporting local `n`-th roots along the
chain multiplies the deck class by `exp(2πi·flux/n)`, where `flux ∈ ℤ` is the net signed
multiplicity that crossed: dominated moves are invisible, an entering zero contributes its
monomial class through the global correction root, a leaving zero divides it out.

Consequently a chain from a nonvanishing member — whose global root gives deck class one —
to `ξ`, with net flux divisible by `2^k`, forces the deck class of `ξ` at the enclosed
zero to be trivial, which is exactly the divisibility clause of the rung `RHLadder k`.
The rung therefore follows from the existence, at every off-line zero and at arbitrarily
small radii, of an anchored ledger chain with even flux: conservation, additivity, jump,
and anchor are all discharged; the burden is the flux parity alone.
-/
import GaloisForLFunctions.RHTower.DeckMultiZero
import GaloisForLFunctions.RHTower.DeckHomotopy
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.BandEdgePairing

namespace RHTower

open Complex Metric

/-! ### Annulus geometry helpers -/

private theorem annulus_radius_lt {a z : ℂ} {r₀ : ℝ} (hz : z ∉ closedBall a r₀) :
    r₀ < ‖z - a‖ := by
  rwa [mem_closedBall, Complex.dist_eq, not_le] at hz

private theorem annulus_ne_center {a z : ℂ} {r₀ : ℝ} (h0 : 0 ≤ r₀)
    (hz : z ∉ closedBall a r₀) : z ≠ a := by
  intro h
  have hlt := annulus_radius_lt hz
  rw [h, sub_self, norm_zero] at hlt
  linarith

private theorem annulus_far {a z ρ' : ℂ} {r₀ : ℝ} (hρ' : ‖ρ' - a‖ ≤ r₀)
    (hz : z ∉ closedBall a r₀) : ‖ρ' - a‖ < ‖z - a‖ :=
  lt_of_le_of_lt hρ' (annulus_radius_lt hz)

private theorem annulus_ne_zero_pt {a z ρ' : ℂ} {r₀ : ℝ} (hρ' : ‖ρ' - a‖ ≤ r₀)
    (hz : z ∉ closedBall a r₀) : z ≠ ρ' := by
  intro h
  have hfar := annulus_far hρ' hz
  rw [h] at hfar
  exact lt_irrefl _ hfar

/-- The standard annulus basepoints `a ± ((r₀+R)/2)·i` lie in both slit annulus charts. -/
theorem annulus_basepoints_mem {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R) :
    (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I ∈ chartRA a r₀ R ∩ chartLA a r₀ R) ∧
      (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I ∈ chartRA a r₀ R ∩ chartLA a r₀ R) := by
  set ε : ℝ := (r₀ + R) / 2 with hε_def
  have hεr : r₀ < ε := by rw [hε_def]; linarith
  have hεR : ε < R := by rw [hε_def]; linarith
  have hεpos : 0 < ε := lt_of_le_of_lt h0 hεr
  set pP := a + ((ε : ℝ) : ℂ) * I with hpP_def
  set pM := a - ((ε : ℝ) : ℂ) * I with hpM_def
  have hPsub : pP - a = ((ε : ℝ) : ℂ) * I := by rw [hpP_def]; ring
  have hMsub : pM - a = -(((ε : ℝ) : ℂ) * I) := by rw [hpM_def]; ring
  have hnormP : ‖pP - a‖ = ε := by
    rw [hPsub, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
      abs_of_pos hεpos]
  have hnormM : ‖pM - a‖ = ε := by
    rw [hMsub, norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hεpos]
  have hannP : pP ∈ ball a R \ closedBall a r₀ := by
    constructor
    · rw [mem_ball, Complex.dist_eq, hnormP]; exact hεR
    · rw [mem_closedBall, Complex.dist_eq, hnormP, not_le]; exact hεr
  have hannM : pM ∈ ball a R \ closedBall a r₀ := by
    constructor
    · rw [mem_ball, Complex.dist_eq, hnormM]; exact hεR
    · rw [mem_closedBall, Complex.dist_eq, hnormM, not_le]; exact hεr
  have himP : (pP - a).im = ε := by rw [hPsub]; simp
  have himM : (pM - a).im = -ε := by rw [hMsub]; simp
  refine ⟨⟨⟨Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [himP]; exact hεpos.ne')), hannP⟩,
      ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hannP⟩⟩,
    ⟨⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hannM⟩,
      ⟨Complex.mem_slitPlane_iff.mpr (Or.inr ?_), hannM⟩⟩⟩
  · have h1 : (a - pP).im = -((pP - a).im) := by simp [Complex.sub_im]
    rw [h1, himP]
    exact neg_ne_zero.mpr hεpos.ne'
  · rw [himM]
    exact neg_ne_zero.mpr hεpos.ne'
  · have h1 : (a - pM).im = -((pM - a).im) := by simp [Complex.sub_im]
    rw [h1, himM]
    simpa using hεpos.ne'

/-! ### Deck-class algebra -/

/-- A single global root pair has trivial deck class. -/
theorem deckClass_self {r : ℂ → ℂ} {pP pM : ℂ} (hP : r pP ≠ 0) (hM : r pM ≠ 0) :
    deckClass r r pP pM = 1 := by
  rw [deckClass, div_self hP, div_self hM, div_self one_ne_zero]

/-- The deck class of pointwise quotients is the quotient of the deck classes. -/
theorem deckClass_div (F F' G G' : ℂ → ℂ) (pP pM : ℂ) :
    deckClass (fun z => F z / F' z) (fun z => G z / G' z) pP pM =
      deckClass F G pP pM / deckClass F' G' pP pM := by
  simp only [deckClass]
  rw [div_div_div_comm (F pP) (F' pP) (G pP) (G' pP),
    div_div_div_comm (F pM) (F' pM) (G pM) (G' pM),
    div_div_div_comm]

/-- `exp(2πi·q/n) = 1` for any integer `q` divisible by `n`. -/
theorem exp_two_pi_mul_int_div_eq_one {n : ℕ} (hn : 0 < n) {q : ℤ}
    (h : (n : ℤ) ∣ q) : exp (2 * (Real.pi : ℂ) * I * (q : ℂ) / n) = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [Complex.exp_eq_one_iff]
  refine ⟨c, ?_⟩
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  push_cast
  rw [mul_div_assoc, mul_comm ((n : ℂ)) ((c : ℂ)), mul_div_assoc, div_self hn0, mul_one]
  ring

/-- The deck class of the paired monomial-times-correction branches at the annulus
basepoints is the monomial class `exp(2πi·m/n)`: the correction root is one global
nonvanishing factor and drops out. -/
private theorem deckClass_mono_corr_pair (a ρ' : ℂ) (m n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    deckClass (fun z => monoRoot₁ a m n z * corrRoot a ρ' m n z)
      (fun z => monoRoot₂ a m n z * corrRoot a ρ' m n z)
      (a + ((ε : ℝ) : ℂ) * I) (a - ((ε : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / n) := by
  have h := deckClass_mul_global (g₁ := monoRoot₁ a m n) (g₂ := monoRoot₂ a m n)
    (r := corrRoot a ρ' m n)
    (corrRoot_ne_zero a ρ' m n (a + ((ε : ℝ) : ℂ) * I))
    (corrRoot_ne_zero a ρ' m n (a - ((ε : ℝ) : ℂ) * I))
  exact h.trans (deckClass_monomial' a m n hε)

/-- Multiplying local roots by the monomial-times-correction branches multiplies the deck
class by the enclosed monomial class `exp(2πi·m/n)`. -/
private theorem deckClass_mul_mono_corr {a ρ' : ℂ} {m n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (G₁ G₂ : ℂ → ℂ) :
    deckClass (fun z => monoRoot₁ a m n z * corrRoot a ρ' m n z * G₁ z)
      (fun z => monoRoot₂ a m n z * corrRoot a ρ' m n z * G₂ z)
      (a + ((ε : ℝ) : ℂ) * I) (a - ((ε : ℝ) : ℂ) * I) =
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / n) *
        deckClass G₁ G₂ (a + ((ε : ℝ) : ℂ) * I) (a - ((ε : ℝ) : ℂ) * I) := by
  have h1 := deckClass_mul (fun z => monoRoot₁ a m n z * corrRoot a ρ' m n z) G₁
    (fun z => monoRoot₂ a m n z * corrRoot a ρ' m n z) G₂
    (a + ((ε : ℝ) : ℂ) * I) (a - ((ε : ℝ) : ℂ) * I)
  exact h1.trans (by rw [deckClass_mono_corr_pair a ρ' m n hε])

/-- Dividing local roots by the monomial-times-correction branches divides the deck class
by the enclosed monomial class `exp(2πi·m/n)`. -/
private theorem deckClass_div_mono_corr {a ρ' : ℂ} {m n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (G₁ G₂ : ℂ → ℂ) :
    deckClass (fun z => G₁ z / (monoRoot₁ a m n z * corrRoot a ρ' m n z))
      (fun z => G₂ z / (monoRoot₂ a m n z * corrRoot a ρ' m n z))
      (a + ((ε : ℝ) : ℂ) * I) (a - ((ε : ℝ) : ℂ) * I) =
      deckClass G₁ G₂ (a + ((ε : ℝ) : ℂ) * I) (a - ((ε : ℝ) : ℂ) * I) /
        exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / n) := by
  have h1 := deckClass_div G₁ (fun z => monoRoot₁ a m n z * corrRoot a ρ' m n z)
    G₂ (fun z => monoRoot₂ a m n z * corrRoot a ρ' m n z)
    (a + ((ε : ℝ) : ℂ) * I) (a - ((ε : ℝ) : ℂ) * I)
  exact h1.trans (by rw [deckClass_mono_corr_pair a ρ' m n hε])

/-! ### The dominated step on annulus charts -/

/-- **Conservation step on the annulus.**  A dominated perturbation of the powered
function transports any local roots to roots of the perturbed function — multiply by the
global correction root of the ratio — with the same deck class at every basepoint pair. -/
theorem deckClass_step_annulus {f g G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f (chartRA a r₀ R ∪ chartLA a r₀ R))
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R))
    (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = g z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = g z)
    (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, ‖f z - g z‖ < ‖g z‖) :
    ∃ H₁ H₂ : ℂ → ℂ, AnalyticOnNhd ℂ H₁ (chartRA a r₀ R) ∧
      AnalyticOnNhd ℂ H₂ (chartLA a r₀ R) ∧
      (∀ z ∈ chartRA a r₀ R, H₁ z ^ n = f z) ∧
      (∀ z ∈ chartLA a r₀ R, H₂ z ^ n = f z) ∧
      ∀ pP pM : ℂ, deckClass H₁ H₂ pP pM = deckClass G₁ G₂ pP pM := by
  refine ⟨fun z => G₁ z * ratioRoot f g n z, fun z => G₂ z * ratioRoot f g n z,
    ?_, ?_, ?_, ?_, fun pP pM =>
      deckClass_mul_global (ratioRoot_ne_zero f g n _) (ratioRoot_ne_zero f g n _)⟩
  · intro z hz
    have hzU : z ∈ chartRA a r₀ R ∪ chartLA a r₀ R := Set.mem_union_left _ hz
    have hcl := hclose z hzU
    have hgan : AnalyticAt ℂ g z :=
      ((hG₁ z hz).pow n).congr (Filter.eventually_of_mem
        ((isOpen_chartRA a r₀ R).mem_nhds hz) (fun y hy => hpG₁ y hy))
    exact (hG₁ z hz).mul (ratioRoot_analyticAt n (hf z hzU) hgan
      (right_ne_zero_of_close hcl) (ratio_mem_slitPlane hcl))
  · intro z hz
    have hzU : z ∈ chartRA a r₀ R ∪ chartLA a r₀ R := Set.mem_union_right _ hz
    have hcl := hclose z hzU
    have hgan : AnalyticAt ℂ g z :=
      ((hG₂ z hz).pow n).congr (Filter.eventually_of_mem
        ((isOpen_chartLA a r₀ R).mem_nhds hz) (fun y hy => hpG₂ y hy))
    exact (hG₂ z hz).mul (ratioRoot_analyticAt n (hf z hzU) hgan
      (right_ne_zero_of_close hcl) (ratio_mem_slitPlane hcl))
  · intro z hz
    have hcl := hclose z (Set.mem_union_left _ hz)
    have hg0 : g z ≠ 0 := right_ne_zero_of_close hcl
    rw [mul_pow, hpG₁ z hz, ratioRoot_pow hn (left_ne_zero_of_close hcl) hg0,
      mul_comm (g z) (f z / g z), div_mul_cancel₀ _ hg0]
  · intro z hz
    have hcl := hclose z (Set.mem_union_right _ hz)
    have hg0 : g z ≠ 0 := right_ne_zero_of_close hcl
    rw [mul_pow, hpG₂ z hz, ratioRoot_pow hn (left_ne_zero_of_close hcl) hg0,
      mul_comm (g z) (f z / g z), div_mul_cancel₀ _ hg0]

/-! ### Ledger chains -/

/-- A ledger chain on the annulus charts of `(a, r₀, R)`: a finite sequence of moves from
one member to another, each move either a dominated perturbation (no zero touches the
charts) or a transversal jump in which the enclosed configuration gains (`jump_in`) or
loses (`jump_out`) one zero of multiplicity `m` inside the hole.  The integer index is the
net signed multiplicity flux through the chart annulus. -/
inductive LedgerChain (a : ℂ) (r₀ R : ℝ) : (ℂ → ℂ) → (ℂ → ℂ) → ℤ → Prop
  | refl (f : ℂ → ℂ) : LedgerChain a r₀ R f f 0
  | dominated {f g h : ℂ → ℂ} {flux : ℤ}
      (hg : AnalyticOnNhd ℂ g (chartRA a r₀ R ∪ chartLA a r₀ R))
      (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, ‖g z - f z‖ < ‖f z‖)
      (rest : LedgerChain a r₀ R g h flux) : LedgerChain a r₀ R f h flux
  | jump_in {f g h : ℂ → ℂ} {ρ' : ℂ} {m : ℕ} {flux : ℤ}
      (hρ' : ‖ρ' - a‖ ≤ r₀)
      (hfact : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, g z = (z - ρ') ^ m * f z)
      (rest : LedgerChain a r₀ R g h flux) : LedgerChain a r₀ R f h (flux + m)
  | jump_out {f g h : ℂ → ℂ} {ρ' : ℂ} {m : ℕ} {flux : ℤ}
      (hρ' : ‖ρ' - a‖ ≤ r₀)
      (hfact : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, f z = (z - ρ') ^ m * g z)
      (rest : LedgerChain a r₀ R g h flux) : LedgerChain a r₀ R f h (flux - m)

/-- **Root transport along a ledger chain.**  Local `n`-th roots of the initial member
transport to local roots of the final member, and the deck class multiplies by exactly
`exp(2πi·flux/n)`: dominated moves preserve the class, an entering zero of multiplicity
`m` multiplies it by `exp(2πi·m/n)` through the monomial and correction roots, a leaving
zero divides it out.  The ledger identity — charge difference ≡ boundary multiplicity
flux mod `n` — in transport form. -/
theorem ledgerChain_transport {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {n : ℕ} (hn : 0 < n) {f g : ℂ → ℂ} {flux : ℤ}
    (hchain : LedgerChain a r₀ R f g flux) :
    ∀ G₁ G₂ : ℂ → ℂ, AnalyticOnNhd ℂ G₁ (chartRA a r₀ R) →
      AnalyticOnNhd ℂ G₂ (chartLA a r₀ R) →
      (∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z) →
      (∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z) →
      ∃ H₁ H₂ : ℂ → ℂ, AnalyticOnNhd ℂ H₁ (chartRA a r₀ R) ∧
        AnalyticOnNhd ℂ H₂ (chartLA a r₀ R) ∧
        (∀ z ∈ chartRA a r₀ R, H₁ z ^ n = g z) ∧
        (∀ z ∈ chartLA a r₀ R, H₂ z ^ n = g z) ∧
        deckClass H₁ H₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
            (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
          exp (2 * (Real.pi : ℂ) * I * (flux : ℂ) / n) *
            deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
              (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := by
  have hε : (0 : ℝ) < (r₀ + R) / 2 := by
    have hR : 0 < R := lt_of_le_of_lt h0 hrR
    linarith
  induction hchain with
  | refl f =>
      intro G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
      refine ⟨G₁, G₂, hG₁, hG₂, hpG₁, hpG₂, ?_⟩
      rw [Int.cast_zero, mul_zero, zero_div, Complex.exp_zero, one_mul]
  | dominated hgan hclose rest ih =>
      intro G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
      obtain ⟨K₁, K₂, hK₁, hK₂, hpK₁, hpK₂, hKG⟩ :=
        deckClass_step_annulus hn hgan hG₁ hG₂ hpG₁ hpG₂ hclose
      obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHK⟩ := ih K₁ K₂ hK₁ hK₂ hpK₁ hpK₂
      exact ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, by rw [hHK, hKG]⟩
  | @jump_in f' g' h' ρ' m flux' hρ' hfact rest ih =>
      intro G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
      have hK₁an : AnalyticOnNhd ℂ
          (fun z => monoRoot₁ a m n z * corrRoot a ρ' m n z * G₁ z)
          (chartRA a r₀ R) := by
        intro z hz
        exact ((monoRoot₁_analyticOnNhd a m n z hz.1).mul
          (corrRoot_analyticAt m n (annulus_ne_center h0 hz.2.2)
            (annulus_far hρ' hz.2.2))).mul (hG₁ z hz)
      have hK₂an : AnalyticOnNhd ℂ
          (fun z => monoRoot₂ a m n z * corrRoot a ρ' m n z * G₂ z)
          (chartLA a r₀ R) := by
        intro z hz
        exact ((monoRoot₂_analyticOnNhd a m n z hz.1).mul
          (corrRoot_analyticAt m n (annulus_ne_center h0 hz.2.2)
            (annulus_far hρ' hz.2.2))).mul (hG₂ z hz)
      have hpK₁ : ∀ z ∈ chartRA a r₀ R,
          (monoRoot₁ a m n z * corrRoot a ρ' m n z * G₁ z) ^ n = g' z := by
        intro z hz
        rw [mul_pow, mul_pow, monoRoot₁_pow hn hz.1,
          corrRoot_pow hn (annulus_far hρ' hz.2.2), hpG₁ z hz, ← mul_pow,
          ← shifted_factor (annulus_ne_center h0 hz.2.2)]
        exact (hfact z (Set.mem_union_left _ hz)).symm
      have hpK₂ : ∀ z ∈ chartLA a r₀ R,
          (monoRoot₂ a m n z * corrRoot a ρ' m n z * G₂ z) ^ n = g' z := by
        intro z hz
        rw [mul_pow, mul_pow, monoRoot₂_pow hn hz.1,
          corrRoot_pow hn (annulus_far hρ' hz.2.2), hpG₂ z hz, ← mul_pow,
          ← shifted_factor (annulus_ne_center h0 hz.2.2)]
        exact (hfact z (Set.mem_union_right _ hz)).symm
      obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHK⟩ := ih _ _ hK₁an hK₂an hpK₁ hpK₂
      refine ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, ?_⟩
      rw [hHK, deckClass_mul_mono_corr hε G₁ G₂, ← mul_assoc, ← Complex.exp_add]
      congr 2
      push_cast
      ring
  | @jump_out f' g' h' ρ' m flux' hρ' hfact rest ih =>
      intro G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
      have hK₁an : AnalyticOnNhd ℂ
          (fun z => G₁ z / (monoRoot₁ a m n z * corrRoot a ρ' m n z))
          (chartRA a r₀ R) := by
        intro z hz
        exact (hG₁ z hz).div ((monoRoot₁_analyticOnNhd a m n z hz.1).mul
          (corrRoot_analyticAt m n (annulus_ne_center h0 hz.2.2)
            (annulus_far hρ' hz.2.2)))
          (mul_ne_zero (Complex.exp_ne_zero _) (corrRoot_ne_zero a ρ' m n z))
      have hK₂an : AnalyticOnNhd ℂ
          (fun z => G₂ z / (monoRoot₂ a m n z * corrRoot a ρ' m n z))
          (chartLA a r₀ R) := by
        intro z hz
        exact (hG₂ z hz).div ((monoRoot₂_analyticOnNhd a m n z hz.1).mul
          (corrRoot_analyticAt m n (annulus_ne_center h0 hz.2.2)
            (annulus_far hρ' hz.2.2)))
          (mul_ne_zero (Complex.exp_ne_zero _) (corrRoot_ne_zero a ρ' m n z))
      have hmono : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R,
          (z - ρ') ^ m ≠ 0 := by
        intro z hz
        have hz2 : z ∉ closedBall a r₀ := by
          rcases hz with hz | hz
          · exact hz.2.2
          · exact hz.2.2
        exact pow_ne_zero m (sub_ne_zero.mpr (annulus_ne_zero_pt hρ' hz2))
      have hpK₁ : ∀ z ∈ chartRA a r₀ R,
          (G₁ z / (monoRoot₁ a m n z * corrRoot a ρ' m n z)) ^ n = g' z := by
        intro z hz
        rw [div_pow, hpG₁ z hz, mul_pow, monoRoot₁_pow hn hz.1,
          corrRoot_pow hn (annulus_far hρ' hz.2.2), ← mul_pow,
          ← shifted_factor (annulus_ne_center h0 hz.2.2),
          hfact z (Set.mem_union_left _ hz),
          mul_div_cancel_left₀ _ (hmono z (Set.mem_union_left _ hz))]
      have hpK₂ : ∀ z ∈ chartLA a r₀ R,
          (G₂ z / (monoRoot₂ a m n z * corrRoot a ρ' m n z)) ^ n = g' z := by
        intro z hz
        rw [div_pow, hpG₂ z hz, mul_pow, monoRoot₂_pow hn hz.1,
          corrRoot_pow hn (annulus_far hρ' hz.2.2), ← mul_pow,
          ← shifted_factor (annulus_ne_center h0 hz.2.2),
          hfact z (Set.mem_union_right _ hz),
          mul_div_cancel_left₀ _ (hmono z (Set.mem_union_right _ hz))]
      obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHK⟩ := ih _ _ hK₁an hK₂an hpK₁ hpK₂
      refine ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, ?_⟩
      have hZ : exp (2 * (Real.pi : ℂ) * I * (((flux' - (m : ℤ)) : ℤ) : ℂ) / n) =
          exp (2 * (Real.pi : ℂ) * I * ((flux' : ℤ) : ℂ) / n) /
            exp (2 * (Real.pi : ℂ) * I * (m : ℂ) / n) := by
        rw [← Complex.exp_sub]
        congr 1
        push_cast
        ring
      rw [hHK, deckClass_div_mono_corr hε G₁ G₂, ← mul_div_assoc, hZ,
        div_mul_eq_mul_div]

/-! ### The anchored ledger and the rung -/

/-- A global `n`-th root exists on a ball where the function does not vanish. -/
theorem exists_global_root_of_nonvanishing {f₀ : ℂ → ℂ} {a : ℂ} {R : ℝ}
    (hR : 0 < R) {n : ℕ} (hn : 0 < n)
    (hf₀ : AnalyticOnNhd ℂ f₀ (ball a R)) (hf₀0 : ∀ z ∈ ball a R, f₀ z ≠ 0) :
    ∃ r : ℂ → ℂ, AnalyticOnNhd ℂ r (ball a R) ∧ ∀ z ∈ ball a R, r z ^ n = f₀ z := by
  have hZloc : ∀ N : ℕ, {w ∈ ball a R ∩ ball a ((N : ℝ) + 1) | f₀ w = 0}.Finite := by
    intro N
    have hempty : {w ∈ ball a R ∩ ball a ((N : ℝ) + 1) | f₀ w = 0} = ∅ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hw
      exact hf₀0 w hw.1
    rw [hempty]
    exact Set.finite_empty
  exact (exists_root_iff_orders_dvd hn isOpen_ball (convex_ball a R) (mem_ball_self hR)
    hf₀ (hf₀0 a (mem_ball_self hR)) hZloc).mpr
    (fun w hw h0' => absurd h0' (hf₀0 w hw))

/-- **The anchored even-flux ledger** for `f` at level `n` on the annulus charts of
`(a, r₀, R)`: a ledger chain from a member that does not vanish on the ball — where the
charge is computably zero — to `f`, whose net signed multiplicity flux through the chart
annulus is divisible by `n`. -/
def AnchoredLedger (n : ℕ) (a : ℂ) (r₀ R : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ (f₀ : ℂ → ℂ) (flux : ℤ),
    AnalyticOnNhd ℂ f₀ (ball a R) ∧ (∀ z ∈ ball a R, f₀ z ≠ 0) ∧
    LedgerChain a r₀ R f₀ f flux ∧ (n : ℤ) ∣ flux

/-- **The ledger computes the charge.**  Under an anchored even-flux ledger, ANY local
`n`-th roots of `f` on the annulus charts have trivial deck class: the anchor's global
root has class one, transport multiplies by `exp(2πi·flux/n) = 1`, and the class does not
depend on the choice of roots. -/
theorem anchoredLedger_deckClass_eq_one {n : ℕ} (hn : 0 < n) {a : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R) {f : ℂ → ℂ}
    (hled : AnchoredLedger n a r₀ R f)
    {K₁ K₂ : ℂ → ℂ}
    (hK₁ : AnalyticOnNhd ℂ K₁ (chartRA a r₀ R))
    (hK₂ : AnalyticOnNhd ℂ K₂ (chartLA a r₀ R))
    (hpK₁ : ∀ z ∈ chartRA a r₀ R, K₁ z ^ n = f z)
    (hpK₂ : ∀ z ∈ chartLA a r₀ R, K₂ z ^ n = f z)
    (hfP : f (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hfM : f (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    deckClass K₁ K₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 := by
  obtain ⟨f₀, flux, hf₀an, hf₀0, hchain, hdvd⟩ := hled
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  obtain ⟨r, hran, hrpow⟩ := exists_global_root_of_nonvanishing hR hn hf₀an hf₀0
  have hsubR : chartRA a r₀ R ⊆ ball a R := fun z hz => hz.2.1
  have hsubL : chartLA a r₀ R ⊆ ball a R := fun z hz => hz.2.1
  obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHcls⟩ :=
    ledgerChain_transport h0 hrR hn hchain r r
      (fun z hz => hran z (hsubR hz)) (fun z hz => hran z (hsubL hz))
      (fun z hz => hrpow z (hsubR hz)) (fun z hz => hrpow z (hsubL hz))
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  have hrP : r (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hPmem.1)
    rw [h0', zero_pow hn.ne'] at this
    exact hf₀0 _ (hsubR hPmem.1) this.symm
  have hrM : r (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hMmem.1)
    rw [h0', zero_pow hn.ne'] at this
    exact hf₀0 _ (hsubR hMmem.1) this.symm
  have hH1 : deckClass H₁ H₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 := by
    rw [hHcls, deckClass_self hrP hrM, mul_one]
    exact exp_two_pi_mul_int_div_eq_one hn hdvd
  have htrans := deckClass_root_indep hn (isOpen_chartRA a r₀ R)
    (isPreconnected_chartRA a h0) (isOpen_chartLA a r₀ R) (isPreconnected_chartLA a h0)
    hH₁ hK₁ hH₂ hK₂ hpH₁ hpK₁ hpH₂ hpK₂
    hPmem.1 hPmem.2 hMmem.1 hMmem.2 hfP hfM
  rw [htrans]
  exact hH1

/-- **The deck class of ξ on annulus charts counts the enclosed multiplicity.**  Around
any point there is `R₀ > 0` such that for all annulus data `0 ≤ r₀ < R ≤ R₀` and every
level `n`, any local `n`-th roots of ξ on the two slit annulus charts have deck class
`exp(2πi·m/n)`, `m` the vanishing order at the center. -/
theorem xi_deckClass_annulus (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ {r₀ R : ℝ}, 0 ≤ r₀ → r₀ < R → R ≤ R₀ → ∀ {n : ℕ}, 0 < n →
      ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartRA ρ₀ r₀ R) → AnalyticOnNhd ℂ G₂ (chartLA ρ₀ r₀ R) →
      (∀ z ∈ chartRA ρ₀ r₀ R, G₁ z ^ n = xi z) →
      (∀ z ∈ chartLA ρ₀ r₀ R, G₂ z ^ n = xi z) →
      deckClass G₁ G₂ (ρ₀ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (ρ₀ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
        exp (2 * (Real.pi : ℂ) * I * ((analyticOrderAt xi ρ₀).toNat : ℂ) / n) := by
  obtain ⟨R₀, hR₀, h, hhan, hh0, hfact⟩ := xi_peel_ball ρ₀
  refine ⟨R₀, hR₀, ?_⟩
  intro r₀ R h0 hrR hRle n hn G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
  have hsub : ball ρ₀ R ⊆ ball ρ₀ R₀ := ball_subset_ball hRle
  have hmz := deckClass_multi_zero (Finset.univ : Finset Unit) (fun _ => ρ₀)
    (fun _ => (analyticOrderAt xi ρ₀).toNat) h0 hrR hn
    (fun _ _ => by simpa using h0)
    (fun z hz => hhan z (hsub hz)) (fun z hz => hh0 z (hsub hz))
    (fun z hz => by
      have hprod : (∏ _i ∈ (Finset.univ : Finset Unit),
          (z - ρ₀) ^ (analyticOrderAt xi ρ₀).toNat) =
          (z - ρ₀) ^ (analyticOrderAt xi ρ₀).toNat := by simp
      rw [hprod]
      exact hfact z (hsub hz))
    hG₁ hG₂ hpG₁ hpG₂
  have hsum : (∑ _i ∈ (Finset.univ : Finset Unit),
      (((analyticOrderAt xi ρ₀).toNat : ℕ) : ℂ)) =
      ((analyticOrderAt xi ρ₀).toNat : ℂ) := by simp
  rw [hsum] at hmz
  exact hmz

/-- **The rung from anchored even-flux ledgers.**  If every hypothetical off-line ξ-zero
admits, at arbitrarily small radii, an anchored ledger chain with net flux divisible by
`2^k`, then every off-line vanishing order is divisible by `2^k`.  Conservation,
additivity, the jump, and the anchor are theorems; the residual burden is exactly the
flux-parity clause of the ledger. -/
theorem rhLadder_of_anchoredLedgers (k : ℕ)
    (hled : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ ε > 0, ∃ r₀ R : ℝ,
      0 ≤ r₀ ∧ r₀ < R ∧ R ≤ ε ∧ AnchoredLedger (2 ^ k) ρ r₀ R xi) :
    RHLadder k := by
  intro ρ hρ hzero
  obtain ⟨R₀, hR₀, hclass⟩ := xi_deckClass_annulus ρ
  obtain ⟨r₀, R, h0, hrR, hRle, f₀, flux, hf₀an, hf₀0, hchain, hdvd⟩ :=
    hled ρ hρ hzero R₀ hR₀
  have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  obtain ⟨r, hran, hrpow⟩ := exists_global_root_of_nonvanishing hR h2k hf₀an hf₀0
  have hsubR : chartRA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  have hsubL : chartLA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  obtain ⟨H₁, H₂, hH₁, hH₂, hpH₁, hpH₂, hHcls⟩ :=
    ledgerChain_transport h0 hrR h2k hchain r r
      (fun z hz => hran z (hsubR hz)) (fun z hz => hran z (hsubL hz))
      (fun z hz => hrpow z (hsubR hz)) (fun z hz => hrpow z (hsubL hz))
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem h0 hrR
  have hrP : r (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hPmem.1)
    rw [h0', zero_pow h2k.ne'] at this
    exact hf₀0 _ (hsubR hPmem.1) this.symm
  have hrM : r (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0 := by
    intro h0'
    have := hrpow _ (hsubR hMmem.1)
    rw [h0', zero_pow h2k.ne'] at this
    exact hf₀0 _ (hsubR hMmem.1) this.symm
  have h1 : deckClass H₁ H₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
      (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) = 1 := by
    rw [hHcls, deckClass_self hrP hrM, mul_one]
    exact exp_two_pi_mul_int_div_eq_one h2k hdvd
  have h2 := hclass h0 hrR hRle h2k hH₁ hH₂ hpH₁ hpH₂
  rw [h1] at h2
  have hdvd2 : 2 ^ k ∣ (analyticOrderAt xi ρ).toNat :=
    (exp_two_pi_mul_div_eq_one_iff h2k _).mp h2.symm
  have hm : (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) = analyticOrderAt xi ρ :=
    ENat.coe_toNat (xi_orderAt_ne_top ρ)
  obtain ⟨c, hc⟩ := hdvd2
  rw [← hm, hc]
  exact ⟨(c : ℕ∞), by push_cast; ring⟩

end RHTower

namespace RHTower

open Complex Metric

/-! ### The event-typed ledger -/

/-- A ledger chain recording its transversal events: the list index collects the signed
multiplicities of the jumps in order, an entering zero contributing `+m` and a leaving
zero `−m`.  Dominated moves record nothing. -/
inductive LedgerChainE (a : ℂ) (r₀ R : ℝ) : (ℂ → ℂ) → (ℂ → ℂ) → List ℤ → Prop
  | refl (f : ℂ → ℂ) : LedgerChainE a r₀ R f f []
  | dominated {f g h : ℂ → ℂ} {L : List ℤ}
      (hg : AnalyticOnNhd ℂ g (chartRA a r₀ R ∪ chartLA a r₀ R))
      (hclose : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, ‖g z - f z‖ < ‖f z‖)
      (rest : LedgerChainE a r₀ R g h L) : LedgerChainE a r₀ R f h L
  | jump_in {f g h : ℂ → ℂ} {ρ' : ℂ} {m : ℕ} {L : List ℤ}
      (hρ' : ‖ρ' - a‖ ≤ r₀)
      (hfact : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, g z = (z - ρ') ^ m * f z)
      (rest : LedgerChainE a r₀ R g h L) : LedgerChainE a r₀ R f h ((m : ℤ) :: L)
  | jump_out {f g h : ℂ → ℂ} {ρ' : ℂ} {m : ℕ} {L : List ℤ}
      (hρ' : ‖ρ' - a‖ ≤ r₀)
      (hfact : ∀ z ∈ chartRA a r₀ R ∪ chartLA a r₀ R, f z = (z - ρ') ^ m * g z)
      (rest : LedgerChainE a r₀ R g h L) : LedgerChainE a r₀ R f h ((-(m : ℤ)) :: L)

/-- An event-typed ledger chain is a ledger chain whose flux is the sum of its recorded
events. -/
theorem ledgerChainE_toChain {a : ℂ} {r₀ R : ℝ} {f g : ℂ → ℂ} {L : List ℤ}
    (h : LedgerChainE a r₀ R f g L) : LedgerChain a r₀ R f g L.sum := by
  induction h with
  | refl f => simpa using LedgerChain.refl f
  | dominated hg hclose rest ih => exact LedgerChain.dominated hg hclose ih
  | @jump_in f' g' h' ρ' m L' hρ' hfact rest ih =>
      have hsum : ((m : ℤ) :: L').sum = L'.sum + m := by
        rw [List.sum_cons]
        ring
      rw [hsum]
      exact LedgerChain.jump_in hρ' hfact ih
  | @jump_out f' g' h' ρ' m L' hρ' hfact rest ih =>
      have hsum : ((-(m : ℤ)) :: L').sum = L'.sum - m := by
        rw [List.sum_cons]
        ring
      rw [hsum]
      exact LedgerChain.jump_out hρ' hfact ih

/-- A list of odd integers has sum congruent to its length modulo two. -/
private theorem two_dvd_sum_sub_length {l : List ℤ}
    (hodd : ∀ x ∈ l, ¬ (2 : ℤ) ∣ x) : (2 : ℤ) ∣ (l.sum - l.length) := by
  induction l with
  | nil => simp
  | cons x t ih =>
      have hx : (2 : ℤ) ∣ (x - 1) := by
        have := hodd x List.mem_cons_self
        omega
      have ht := ih (fun y hy => hodd y (List.mem_cons_of_mem x hy))
      rw [List.sum_cons, List.length_cons]
      push_cast
      omega

/-- **The paired-flux interface.**  An event list has paired flux when, up to
permutation, it splits into a part of even events and a part of odd events whose
positions carry a fixed-point-free involutive pairing: every odd transversal event
belongs to a two-element orbit.  The involution's payload is the finite pairing
structure of the band-edge algebra. -/
def LedgerFluxPaired (L : List ℤ) : Prop :=
  ∃ evens odds : List ℤ,
    L.Perm (odds ++ evens) ∧ (∀ x ∈ evens, (2 : ℤ) ∣ x) ∧
    (∀ x ∈ odds, ¬ (2 : ℤ) ∣ x) ∧
    Nonempty (BandEdgePairing (Fin odds.length))

/-- **Paired flux is even.**  The even events contribute nothing modulo two, and the
fixed-point-free pairing forces an even count of odd events, whose sum is congruent to
that count. -/
theorem ledgerFluxPaired_two_dvd_sum {L : List ℤ} (h : LedgerFluxPaired L) :
    (2 : ℤ) ∣ L.sum := by
  obtain ⟨evens, odds, hperm, hev, hodd, ⟨P⟩⟩ := h
  have hlen : 2 ∣ odds.length := by
    have hcard := fixedPointFreePairing_two_dvd_card (Event := Fin odds.length) P
    simpa using hcard
  have hodds : (2 : ℤ) ∣ odds.sum := by
    have h1 := two_dvd_sum_sub_length hodd
    have h2 : (2 : ℤ) ∣ (odds.length : ℤ) := by exact_mod_cast hlen
    omega
  have hevens : (2 : ℤ) ∣ evens.sum := List.dvd_sum hev
  rw [hperm.sum_eq, List.sum_append]
  exact dvd_add hodds hevens

/-- **The event-certified anchored ledger**: an event-typed chain from a nonvanishing
member whose event list has paired flux. -/
def AnchoredEventLedger (a : ℂ) (r₀ R : ℝ) (f : ℂ → ℂ) : Prop :=
  ∃ (f₀ : ℂ → ℂ) (L : List ℤ),
    AnalyticOnNhd ℂ f₀ (ball a R) ∧ (∀ z ∈ ball a R, f₀ z ≠ 0) ∧
    LedgerChainE a r₀ R f₀ f L ∧ LedgerFluxPaired L

/-- An event-certified anchored ledger is an anchored even-flux ledger at level two. -/
theorem anchoredLedger_two_of_eventLedger {a : ℂ} {r₀ R : ℝ} {f : ℂ → ℂ}
    (h : AnchoredEventLedger a r₀ R f) : AnchoredLedger 2 a r₀ R f := by
  obtain ⟨f₀, L, han, hne, hchain, hpar⟩ := h
  exact ⟨f₀, L.sum, han, hne, ledgerChainE_toChain hchain,
    by exact_mod_cast ledgerFluxPaired_two_dvd_sum hpar⟩

/-- **The base rung from event-certified ledgers.**  If every hypothetical off-line
ξ-zero admits, at arbitrarily small radii, an anchored event-typed ledger chain whose
odd transversal events carry a fixed-point-free pairing and whose remaining events are
even, then every off-line vanishing order is even.  The parity burden splits along the
event classes: even events are the seam-certified class, and the pairing of the odd
class is the band-edge interface. -/
theorem rhLadder_one_of_anchoredEventLedgers
    (hled : ∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ ε > 0, ∃ r₀ R : ℝ,
      0 ≤ r₀ ∧ r₀ < R ∧ R ≤ ε ∧ AnchoredEventLedger ρ r₀ R xi) :
    RHLadder 1 := by
  refine rhLadder_of_anchoredLedgers 1 ?_
  intro ρ hρ h0 ε hε
  obtain ⟨r₀, R, h1, h2, h3, hAE⟩ := hled ρ hρ h0 ε hε
  refine ⟨r₀, R, h1, h2, h3, ?_⟩
  rw [pow_one]
  exact anchoredLedger_two_of_eventLedger hAE

end RHTower
