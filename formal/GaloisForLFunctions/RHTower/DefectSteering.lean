/-
Quantified steering of the anchor's mirror defect, and what it turns.

The mirror defect is additive over the prime set: each new prime advances it by an
increment `primeTilt q (1−s̄) + primeTilt q s` whose SIGN is the sign of
`sin(Im s · log q)` — at every height off the discrete vanishing set the two tilt terms
share it, because the imaginary part of an Euler factor is `q^{−Re s}·sin(Im s·log q)`
at every real part — and whose size is pinned between explicit arctangent bounds.  At
square-root level the turning is exact: the canonical root `√‖A‖·e^{i·tilt/2}` of the
anchor pairs across the critical line with a rotation by exactly HALF the mirror
defect.  What the anchor does NOT turn is the deck cocycle: it is a unit with a global
square root on the strip ball, so anchoring a member multiplies both chart roots by one
global function and the two-point deck class — the parity certificate — is invariant.
The defect is therefore precisely the steerable, sign-readable, prime-indexed phase
datum riding on top of an anchor-rigid parity class.
-/
import GaloisForLFunctions.RHTower.FiniteMemberSteering

noncomputable section

namespace RHTower

open Complex Metric

/-! ### §1 The Euler factor's imaginary part and the tilt's sign -/

/-- The imaginary part of an Euler factor at any point: `q^{−Re s}·sin(Im s·log q)`. -/
theorem im_eulerFactor {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    ((1 : ℂ) - (p : ℂ) ^ (-s)).im = (p : ℝ) ^ (-s.re) * Real.sin (s.im * Real.log p) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [show ((p : ℕ) : ℂ) = (((p : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log hppos.le]
  rw [Complex.cpow_def_of_ne_zero hpne, hlog]
  have hexp : ((Real.log p : ℝ) : ℂ) * (-s)
      = ((-(Real.log p * s.re) : ℝ) : ℂ) + ((-(s.im * Real.log p) : ℝ) : ℂ) * I := by
    conv_lhs => rw [← Complex.re_add_im s]
    push_cast
    ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp,
    Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, Real.sin_neg,
    Real.rpow_def_of_pos hppos]
  ring_nf

/-- The arctangent is negative exactly on negative inputs. -/
theorem arctan_neg_iff {x : ℝ} : Real.arctan x < 0 ↔ x < 0 := by
  rw [← neg_pos, ← Real.arctan_neg, Real.arctan_pos, neg_pos]

/-- **The tilt's sign is the sign of `sin(Im s·log p)`** — positive side. -/
theorem primeTilt_pos_iff {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    0 < primeTilt p s ↔ 0 < Real.sin (s.im * Real.log p) := by
  have hre := re_eulerFactor_pos hp hs
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-s.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p)) _
  rw [primeTilt, arg_eq_arctan_of_re_pos hre, Real.arctan_pos,
    div_pos_iff_of_pos_right hre, im_eulerFactor hp]
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_pos hrp h

/-- **The tilt's sign is the sign of `sin(Im s·log p)`** — negative side. -/
theorem primeTilt_neg_iff {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    primeTilt p s < 0 ↔ Real.sin (s.im * Real.log p) < 0 := by
  have hre := re_eulerFactor_pos hp hs
  have hrp : (0 : ℝ) < (p : ℝ) ^ (-s.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p)) _
  rw [primeTilt, arg_eq_arctan_of_re_pos hre, arctan_neg_iff]
  have hdiv : ((1 : ℂ) - (p : ℂ) ^ (-s)).im / ((1 : ℂ) - (p : ℂ) ^ (-s)).re < 0
      ↔ ((1 : ℂ) - (p : ℂ) ^ (-s)).im < 0 := by
    constructor
    · intro h
      by_contra hge
      have := div_nonneg (not_lt.mp hge) hre.le
      linarith
    · intro h
      exact div_neg_of_neg_of_pos h hre
  rw [hdiv, im_eulerFactor hp]
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_neg_of_pos_of_neg hrp h

/-! ### §2 Additivity: the defect as a prime-indexed walk -/

/-- The mirror increment of a single prime: what adjoining `q` adds to the defect. -/
def mirrorTiltIncrement (q : ℕ) (s : ℂ) : ℝ :=
  primeTilt q (1 - (starRingEnd ℂ) s) + primeTilt q s

theorem anchorMirrorDefect_empty (s : ℂ) : anchorMirrorDefect ∅ s = 0 := by
  unfold anchorMirrorDefect anchorTilt
  simp

theorem anchorMirrorDefect_singleton (q : ℕ) (s : ℂ) :
    anchorMirrorDefect {q} s = mirrorTiltIncrement q s := by
  unfold anchorMirrorDefect anchorTilt mirrorTiltIncrement
  simp

/-- **The defect is additive over the prime set**: each new prime advances it by its
mirror increment. -/
theorem anchorMirrorDefect_insert {q : ℕ} {P : Finset ℕ} (hq : q ∉ P) (s : ℂ) :
    anchorMirrorDefect (insert q P) s
      = mirrorTiltIncrement q s + anchorMirrorDefect P s := by
  unfold anchorMirrorDefect anchorTilt mirrorTiltIncrement
  rw [Finset.sum_insert hq, Finset.sum_insert hq]
  ring

/-! ### §3 The increment's sign and size: the steering laws -/

/-- **Positive steering**: at any strip point with `sin(Im s·log q) > 0` the mirror
increment of `q` is strictly positive — BOTH tilt terms are, since the reflected point
has the same imaginary part and complementary real part. -/
theorem mirrorTiltIncrement_pos {q : ℕ} (hq : 2 ≤ q) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hsin : 0 < Real.sin (s.im * Real.log q)) :
    0 < mirrorTiltIncrement q s := by
  have hre' : 0 < (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have him' : (1 - (starRingEnd ℂ) s).im = s.im := by
    simp [Complex.sub_im, Complex.conj_im]
  have h1' : 0 < primeTilt q (1 - (starRingEnd ℂ) s) := by
    rw [primeTilt_pos_iff hq hre', him']
    exact hsin
  have h2' : 0 < primeTilt q s := (primeTilt_pos_iff hq h0).mpr hsin
  unfold mirrorTiltIncrement
  linarith

/-- **Negative steering**: at any strip point with `sin(Im s·log q) < 0` the mirror
increment of `q` is strictly negative. -/
theorem mirrorTiltIncrement_neg {q : ℕ} (hq : 2 ≤ q) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hsin : Real.sin (s.im * Real.log q) < 0) :
    mirrorTiltIncrement q s < 0 := by
  have hre' : 0 < (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have him' : (1 - (starRingEnd ℂ) s).im = s.im := by
    simp [Complex.sub_im, Complex.conj_im]
  have h1' : primeTilt q (1 - (starRingEnd ℂ) s) < 0 := by
    rw [primeTilt_neg_iff hq hre', him']
    exact hsin
  have h2' : primeTilt q s < 0 := (primeTilt_neg_iff hq h0).mpr hsin
  unfold mirrorTiltIncrement
  linarith

/-- **The quantified turn, from below**: with `sin(Im s·log q) > 0` the increment is at
least `arctan(q^{−Re s}·sin(Im s·log q)/2)` — the factor's real part never exceeds 2,
so the tilt beats the arctangent of half the imaginary part. -/
theorem mirrorTiltIncrement_ge {q : ℕ} (hq : 2 ≤ q) {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1)
    (hsin : 0 < Real.sin (s.im * Real.log q)) :
    Real.arctan ((q : ℝ) ^ (-s.re) * Real.sin (s.im * Real.log q) / 2)
      ≤ mirrorTiltIncrement q s := by
  have hre := re_eulerFactor_pos hq h0
  have hreh : ((1 : ℂ) - (q : ℂ) ^ (-s)).re ≤ 2 := by
    have habs := Complex.abs_re_le_norm ((q : ℂ) ^ (-s))
    rw [norm_prime_cpow_neg hq s] at habs
    have hle1 : (q : ℝ) ^ (-s.re) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast (by omega : 1 ≤ q)) (by linarith)
    have hneg := neg_le_abs (((q : ℂ) ^ (-s)).re)
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have him : ((1 : ℂ) - (q : ℂ) ^ (-s)).im
      = (q : ℝ) ^ (-s.re) * Real.sin (s.im * Real.log q) := im_eulerFactor hq s
  have hrp : (0 : ℝ) < (q : ℝ) ^ (-s.re) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < q)) _
  have himpos : 0 < ((1 : ℂ) - (q : ℂ) ^ (-s)).im := by
    rw [him]
    exact mul_pos hrp hsin
  have hstep : (q : ℝ) ^ (-s.re) * Real.sin (s.im * Real.log q) / 2
      ≤ ((1 : ℂ) - (q : ℂ) ^ (-s)).im / ((1 : ℂ) - (q : ℂ) ^ (-s)).re := by
    rw [← him]
    exact div_le_div_of_nonneg_left himpos.le hre hreh
  have h2' : Real.arctan ((q : ℝ) ^ (-s.re) * Real.sin (s.im * Real.log q) / 2)
      ≤ primeTilt q s := by
    rw [primeTilt, arg_eq_arctan_of_re_pos hre]
    exact Real.arctan_mono hstep
  have hre' : 0 < (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have him' : (1 - (starRingEnd ℂ) s).im = s.im := by
    simp [Complex.sub_im, Complex.conj_im]
  have h1' : 0 < primeTilt q (1 - (starRingEnd ℂ) s) := by
    rw [primeTilt_pos_iff hq hre', him']
    exact hsin
  unfold mirrorTiltIncrement
  linarith

/-- **The quantified turn, from above**: on a symmetric strip band the increment is
bounded by twice the single-prime budget. -/
theorem abs_mirrorTiltIncrement_le {q : ℕ} (hq : 2 ≤ q) {s : ℂ} {σ₀ : ℝ}
    (h0 : 0 < σ₀) (hσ : σ₀ ≤ s.re) (hσ' : σ₀ ≤ 1 - s.re) :
    |mirrorTiltIncrement q s| ≤ 2 * ((q : ℝ) ^ (-σ₀) / (1 - (q : ℝ) ^ (-σ₀))) := by
  have hσm : σ₀ ≤ (1 - (starRingEnd ℂ) s).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have h1 := abs_primeTilt_le hq h0 hσm
  have h2 := abs_primeTilt_le hq h0 hσ
  unfold mirrorTiltIncrement
  refine le_trans (abs_add_le _ _) ?_
  linarith

/-! ### §4 The canonical anchor root and the exact half-defect turning -/

/-- The canonical square root of the anchor: modulus root times half-tilt phase. -/
def canonicalAnchorRoot (P : Finset ℕ) (s : ℂ) : ℂ :=
  ((Real.sqrt ‖eulerHeadAnchor P s‖ : ℝ) : ℂ)
    * Complex.exp (((anchorTilt P s / 2 : ℝ) : ℂ) * I)

/-- The canonical root squares to the anchor — via the polar identity. -/
theorem canonicalAnchorRoot_sq (P : Finset ℕ) (s : ℂ) :
    canonicalAnchorRoot P s ^ 2 = eulerHeadAnchor P s := by
  unfold canonicalAnchorRoot
  rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg _), sq,
    ← Complex.exp_add,
    show ((anchorTilt P s / 2 : ℝ) : ℂ) * I + ((anchorTilt P s / 2 : ℝ) : ℂ) * I
      = ((anchorTilt P s : ℝ) : ℂ) * I from by push_cast; ring]
  exact (eulerHeadAnchor_polar P s).symm

theorem canonicalAnchorRoot_ne_zero {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ}
    (hs : 0 < s.re) :
    canonicalAnchorRoot P s ≠ 0 := by
  unfold canonicalAnchorRoot
  apply mul_ne_zero
  · rw [Complex.ofReal_ne_zero]
    exact Real.sqrt_ne_zero'.mpr (norm_pos_iff.mpr (eulerHeadAnchor_ne_zero hP hs))
  · exact Complex.exp_ne_zero _

/-- **The exact turning law at root level**: across the critical line the canonical
anchor roots pair with a rotation by exactly HALF the mirror defect — the boundary
phase of `√A`, and hence of any root of the anchored member, turns by `defect/2`. -/
theorem canonicalAnchorRoot_mul_mirror (P : Finset ℕ) (s : ℂ) :
    canonicalAnchorRoot P (1 - (starRingEnd ℂ) s) * canonicalAnchorRoot P s
      = ((Real.sqrt (‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖
            * ‖eulerHeadAnchor P s‖) : ℝ) : ℂ)
        * Complex.exp (((anchorMirrorDefect P s / 2 : ℝ) : ℂ) * I) := by
  unfold canonicalAnchorRoot
  rw [mul_mul_mul_comm, ← Complex.ofReal_mul, ← Real.sqrt_mul (norm_nonneg _),
    ← Complex.exp_add,
    show ((anchorTilt P (1 - (starRingEnd ℂ) s) / 2 : ℝ) : ℂ) * I
        + ((anchorTilt P s / 2 : ℝ) : ℂ) * I
      = ((anchorMirrorDefect P s / 2 : ℝ) : ℂ) * I from by
        rw [anchorMirrorDefect]
        push_cast
        ring]

/-! ### §5 What the defect does NOT turn: the deck class is anchor-rigid -/

/-- **Anchoring turns phases, not the parity class.**  From any chart square roots of
the symmetric member, multiplying by a global square root of the anchor — which exists
on the strip ball because the anchor is a nonvanishing unit there — produces chart
square roots of the anchored member with the SAME deck class.  The defect angle steers
the boundary phase data while the two-point parity certificate is anchor-invariant. -/
theorem anchoredSEM_roots_of_sem_roots {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {ρ : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hstripb : ∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1)
    {N : ℕ} {H₁ H₂ : ℂ → ℂ}
    (hH₁ : AnalyticOnNhd ℂ H₁ (chartRA ρ r₀ R))
    (hH₂ : AnalyticOnNhd ℂ H₂ (chartLA ρ r₀ R))
    (hpH₁ : ∀ z ∈ chartRA ρ r₀ R, H₁ z ^ 2 = completedSEM N z)
    (hpH₂ : ∀ z ∈ chartLA ρ r₀ R, H₂ z ^ 2 = completedSEM N z) :
    ∃ G₁ G₂ : ℂ → ℂ,
      AnalyticOnNhd ℂ G₁ (chartRA ρ r₀ R) ∧ AnalyticOnNhd ℂ G₂ (chartLA ρ r₀ R) ∧
      (∀ z ∈ chartRA ρ r₀ R, G₁ z ^ 2 = anchoredSEM P N z) ∧
      (∀ z ∈ chartLA ρ r₀ R, G₂ z ^ 2 = anchoredSEM P N z) ∧
      deckClass G₁ G₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = deckClass H₁ H₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
            (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) := by
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  have hAan : AnalyticOnNhd ℂ (eulerHeadAnchor P) (ball ρ R) := fun z _ =>
    eulerHeadAnchor_analyticAt hP z
  have hAne : ∀ z ∈ ball ρ R, eulerHeadAnchor P z ≠ 0 := fun z hz =>
    eulerHeadAnchor_ne_zero hP (hstripb z hz).1
  obtain ⟨r, hran, hrpow⟩ :=
    exists_global_root_of_nonvanishing hR (by norm_num : (0 : ℕ) < 2) hAan hAne
  have hsubR : chartRA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  have hsubL : chartLA ρ r₀ R ⊆ ball ρ R := fun z hz => hz.2.1
  have hrne : ∀ z ∈ ball ρ R, r z ≠ 0 := by
    intro z hz h
    have hpow := hrpow z hz
    rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hpow
    exact hAne z hz hpow.symm
  obtain ⟨hPmem, hMmem⟩ := annulus_basepoints_mem (a := ρ) h0 hrR
  refine ⟨fun z => H₁ z * r z, fun z => H₂ z * r z,
    fun z hz => (hH₁ z hz).mul (hran z (hsubR hz)),
    fun z hz => (hH₂ z hz).mul (hran z (hsubL hz)), ?_, ?_, ?_⟩
  · intro z hz
    show (H₁ z * r z) ^ 2 = anchoredSEM P N z
    unfold anchoredSEM
    rw [mul_pow, hpH₁ z hz, hrpow z (hsubR hz), mul_comm]
  · intro z hz
    show (H₂ z * r z) ^ 2 = anchoredSEM P N z
    unfold anchoredSEM
    rw [mul_pow, hpH₂ z hz, hrpow z (hsubL hz), mul_comm]
  · exact deckClass_mul_global (hrne _ (hsubR hPmem.1)) (hrne _ (hsubR hMmem.1))

end RHTower
