/-
The anchor's phase tilt and its mirror defect.

Each Euler factor `1 − p^{−s}` lies in the open right half plane for `Re s > 0` (its
distance to `1` is `p^{−Re s} < 1`), so its principal argument is the smooth angle
`arctan(Im/Re)` in `(−π/2, π/2)`.  The anchor tilt is the sum of these angles over the
finite prime set — the canonical phase branch of the finite Euler head.  It satisfies an
exact polar identity (the anchor IS its modulus times `exp(i·tilt)`) and a height-uniform
budget `|tilt| ≤ ∑ p^{−σ₀}/(1−p^{−σ₀})`: the anchor's log-derivative budget with `log p`
replaced by `1`.

The mirror defect is the tilt at the line-reflected point `1−s̄` plus the tilt at `s`.
For a line-reflection equivariant function the corresponding quantity is quantized in
`2πℤ`; the defect measures the anchor's failure of equivariance exactly, through the
product identity `A(1−s̄)·A(s) = ‖A(1−s̄)‖·‖A(s)‖·exp(i·defect)`.  The main law: the
anchored incidence value at the mirror point is the blind reversal (the conjugate)
rotated by exactly minus the defect, up to a positive modulus ratio — the entire
departure of the anchored pencil from the mirror-blind law is carried by one real angle,
bounded uniformly on any ball inside the strip, in particular on the isolating annulus of
a hypothetical off-line zero where the paired-flux consumer reads its boundary data.

On the critical line the reflection fixes every point and equivariance forces reality:
the single-prime anchor has imaginary part `p^{−1/2}·sin(τ·log p)` there, so at every
height with `sin(τ·log p) ≠ 0` the anchor fails the equivariance hypothesis of the
mirror-blindness theorems.  The anchor de-symmetrizes the pencil at all heights off a
discrete set.
-/
import GaloisForLFunctions.RHTower.AnchorHead
import GaloisForLFunctions.RHTower.MirrorEdgeSymmetry
import GaloisForLFunctions.HTGeometry.SectorPowerMassLower

open Complex Metric

namespace RHTower

/-! ### The tilt and its budget -/

/-- The tilt of a single Euler factor: the principal argument of `1 − p^{−s}`. -/
noncomputable def primeTilt (p : ℕ) (s : ℂ) : ℝ := ((1 : ℂ) - (p : ℂ) ^ (-s)).arg

/-- The anchor's phase tilt: the summed factor angles over the prime set. -/
noncomputable def anchorTilt (P : Finset ℕ) (s : ℂ) : ℝ := ∑ p ∈ P, primeTilt p s

/-- The mirror defect: the tilt at the line-reflected point plus the tilt at the point.
For a line-reflection equivariant function this combination is quantized in `2πℤ`; the
defect measures the anchor's phase asymmetry across the critical line. -/
noncomputable def anchorMirrorDefect (P : Finset ℕ) (s : ℂ) : ℝ :=
  anchorTilt P (1 - (starRingEnd ℂ) s) + anchorTilt P s

/-- The height-uniform tilt budget: the anchor budget with `log p` replaced by `1`. -/
noncomputable def tiltBudget (P : Finset ℕ) (σ : ℝ) : ℝ :=
  ∑ p ∈ P, (p : ℝ) ^ (-σ) / (1 - (p : ℝ) ^ (-σ))

/-! ### Factor geometry: the right half plane -/

/-- The norm of the Euler variable. -/
theorem norm_prime_cpow_neg {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hpr, Complex.neg_re]

/-- The real part of an Euler factor sits above `1 − p^{−Re s}`. -/
private theorem re_eulerFactor_ge {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    1 - (p : ℝ) ^ (-s.re) ≤ ((1 : ℂ) - (p : ℂ) ^ (-s)).re := by
  have h1 : ((1 : ℂ) - (p : ℂ) ^ (-s)).re = 1 - ((p : ℂ) ^ (-s)).re := by
    rw [Complex.sub_re, Complex.one_re]
  rw [h1, ← norm_prime_cpow_neg hp s]
  have := Complex.re_le_norm ((p : ℂ) ^ (-s))
  linarith

/-- Each Euler factor lies in the open right half plane on `Re s > 0`. -/
theorem re_eulerFactor_pos {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    0 < ((1 : ℂ) - (p : ℂ) ^ (-s)).re := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlt : (p : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  linarith [re_eulerFactor_ge hp s]

/-- The imaginary part of an Euler factor is dominated by `p^{−Re s}`. -/
private theorem abs_im_eulerFactor_le {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    |((1 : ℂ) - (p : ℂ) ^ (-s)).im| ≤ (p : ℝ) ^ (-s.re) := by
  have h1 : ((1 : ℂ) - (p : ℂ) ^ (-s)).im = -((p : ℂ) ^ (-s)).im := by
    rw [Complex.sub_im, Complex.one_im]
    ring
  rw [h1, abs_neg, ← norm_prime_cpow_neg hp s]
  exact Complex.abs_im_le_norm _

/-! ### The argument as a smooth angle -/

/-- On the open right half plane the principal argument is `arctan(Im/Re)`. -/
theorem arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) :=
  GaloisForLFunctions.HTGeometry.complexArg_eq_arctan_of_re_pos hz

/-- The arctangent is dominated by its argument in absolute value. -/
private theorem abs_arctan_le_abs (x : ℝ) : |Real.arctan x| ≤ |x| := by
  have key : ∀ y : ℝ, 0 ≤ y → Real.arctan y ≤ y := by
    intro y hy
    rcases eq_or_lt_of_le hy with h | h
    · rw [← h, Real.arctan_zero]
    · exact (lt_of_lt_of_eq
        (Real.lt_tan (Real.arctan_pos.mpr h) (Real.arctan_lt_pi_div_two y))
        (Real.tan_arctan y)).le
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, abs_of_nonneg]
    · exact key x hx
    · rcases eq_or_lt_of_le hx with h | h
      · rw [← h, Real.arctan_zero]
      · exact (Real.arctan_pos.mpr h).le
  · have hx' : x < 0 := lt_of_not_ge hx
    have hkey := key (-x) (by linarith)
    rw [Real.arctan_neg] at hkey
    rw [abs_of_neg hx', abs_of_neg]
    · linarith
    · have : 0 < Real.arctan (-x) := Real.arctan_pos.mpr (by linarith)
      rw [Real.arctan_neg] at this
      linarith

/-- **The per-prime tilt budget, uniform in height.**  On `Re s ≥ σ₀ > 0` the tilt of a
single Euler factor is at most `p^{−σ₀}/(1−p^{−σ₀})`. -/
theorem abs_primeTilt_le {p : ℕ} (hp : 2 ≤ p) {s : ℂ} {σ₀ : ℝ}
    (h0 : 0 < σ₀) (hσ : σ₀ ≤ s.re) :
    |primeTilt p s| ≤ (p : ℝ) ^ (-σ₀) / (1 - (p : ℝ) ^ (-σ₀)) := by
  have hs : 0 < s.re := lt_of_lt_of_le h0 hσ
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hmono : (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-σ₀) :=
    Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hlt0 : (p : ℝ) ^ (-σ₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
  have hrepos := re_eulerFactor_pos hp hs
  have hre : 1 - (p : ℝ) ^ (-σ₀) ≤ ((1 : ℂ) - (p : ℂ) ^ (-s)).re := by
    have := re_eulerFactor_ge hp s
    linarith
  have him : |((1 : ℂ) - (p : ℂ) ^ (-s)).im| ≤ (p : ℝ) ^ (-σ₀) :=
    le_trans (abs_im_eulerFactor_le hp s) hmono
  have harg : primeTilt p s =
      Real.arctan (((1 : ℂ) - (p : ℂ) ^ (-s)).im / ((1 : ℂ) - (p : ℂ) ^ (-s)).re) :=
    arg_eq_arctan_of_re_pos hrepos
  rw [harg]
  refine le_trans (abs_arctan_le_abs _) ?_
  rw [abs_div, abs_of_pos hrepos]
  exact div_le_div₀ (by positivity) him (by linarith) hre

/-- **The anchor tilt budget, uniform in height.** -/
theorem abs_anchorTilt_le {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} {σ₀ : ℝ}
    (h0 : 0 < σ₀) (hσ : σ₀ ≤ s.re) :
    |anchorTilt P s| ≤ tiltBudget P σ₀ := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
  intro p hp
  exact abs_primeTilt_le (hP p hp) h0 hσ

/-! ### Schwarz oddness of the tilt -/

/-- The Euler variable conjugates with the point. -/
private theorem prime_cpow_neg_conj {p : ℕ} (hp : 2 ≤ p) (s : ℂ) :
    (p : ℂ) ^ (-(starRingEnd ℂ) s) = (starRingEnd ℂ) ((p : ℂ) ^ (-s)) := by
  have hpne : (p : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega)
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [show ((p : ℕ) : ℂ) = (((p : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  rw [Complex.cpow_def_of_ne_zero hpne, Complex.cpow_def_of_ne_zero hpne, hlog,
    ← Complex.exp_conj, map_mul, Complex.conj_ofReal, map_neg]

/-- The per-prime tilt is Schwarz-odd. -/
theorem primeTilt_conj {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    primeTilt p ((starRingEnd ℂ) s) = -primeTilt p s := by
  have hfac : (1 : ℂ) - (p : ℂ) ^ (-(starRingEnd ℂ) s) =
      (starRingEnd ℂ) ((1 : ℂ) - (p : ℂ) ^ (-s)) := by
    rw [prime_cpow_neg_conj hp, map_sub, map_one]
  have hargne : ((1 : ℂ) - (p : ℂ) ^ (-s)).arg ≠ Real.pi := by
    intro h
    have := (Complex.arg_eq_pi_iff.mp h).1
    linarith [re_eulerFactor_pos hp hs]
  unfold primeTilt
  rw [hfac, Complex.arg_conj, if_neg hargne]

/-- The anchor tilt is Schwarz-odd. -/
theorem anchorTilt_conj {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    anchorTilt P ((starRingEnd ℂ) s) = -anchorTilt P s := by
  unfold anchorTilt
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun p hp => primeTilt_conj (hP p hp) hs

/-! ### The exact polar identity -/

/-- A finite product recomposes from its factor moduli and summed factor angles. -/
private theorem prod_polar (P : Finset ℕ) (f : ℕ → ℂ) :
    ∏ p ∈ P, f p =
      ((∏ p ∈ P, ‖f p‖ : ℝ) : ℂ) * Complex.exp (((∑ p ∈ P, (f p).arg : ℝ) : ℂ) * I) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.prod_insert ha, Finset.sum_insert ha]
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I (f a)]
      rw [show ((((f a).arg + ∑ p ∈ s, (f p).arg : ℝ)) : ℂ) * I =
          ((f a).arg : ℂ) * I + ((∑ p ∈ s, (f p).arg : ℝ) : ℂ) * I by push_cast; ring,
        Complex.exp_add]
      push_cast
      ring

/-- **The anchor's polar identity**: the finite Euler head is its modulus times the
exponential of its tilt — the tilt is the canonical phase branch of the anchor. -/
theorem eulerHeadAnchor_polar (P : Finset ℕ) (s : ℂ) :
    eulerHeadAnchor P s =
      ((‖eulerHeadAnchor P s‖ : ℝ) : ℂ) * Complex.exp (((anchorTilt P s : ℝ) : ℂ) * I) := by
  unfold eulerHeadAnchor anchorTilt primeTilt
  rw [norm_prod]
  exact prod_polar P _

/-- **The mirror product identity**: the anchor value at the reflected point times the
value at the point equals the product of the two moduli rotated by exactly the mirror
defect.  The entire phase asymmetry of the anchor across the critical line is the
defect. -/
theorem eulerHeadAnchor_mul_mirror (P : Finset ℕ) (s : ℂ) :
    eulerHeadAnchor P (1 - (starRingEnd ℂ) s) * eulerHeadAnchor P s =
      ((‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖ * ‖eulerHeadAnchor P s‖ : ℝ) : ℂ) *
        Complex.exp (((anchorMirrorDefect P s : ℝ) : ℂ) * I) := by
  conv_lhs => rw [eulerHeadAnchor_polar P (1 - (starRingEnd ℂ) s),
    eulerHeadAnchor_polar P s]
  rw [anchorMirrorDefect,
    show (((anchorTilt P (1 - (starRingEnd ℂ) s) + anchorTilt P s : ℝ)) : ℂ) * I =
      ((anchorTilt P (1 - (starRingEnd ℂ) s) : ℝ) : ℂ) * I +
        ((anchorTilt P s : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add]
  push_cast
  ring

/-- **Equivariance quantizes the defect.**  If the anchor were line-reflection
equivariant at `s` — the hypothesis of every mirror-blindness theorem — its mirror
defect would lie in `2πℤ`. -/
theorem anchorMirrorDefect_int_of_lineReflection {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {s : ℂ} (hs : 0 < s.re)
    (heq : eulerHeadAnchor P (1 - (starRingEnd ℂ) s) =
      (starRingEnd ℂ) (eulerHeadAnchor P s)) :
    ∃ n : ℤ, anchorMirrorDefect P s = n * (2 * Real.pi) := by
  have hA : eulerHeadAnchor P s ≠ 0 := eulerHeadAnchor_ne_zero hP hs
  have hAn : (0 : ℝ) < ‖eulerHeadAnchor P s‖ := norm_pos_iff.mpr hA
  have hkey := eulerHeadAnchor_mul_mirror P s
  rw [heq, Complex.norm_conj] at hkey
  have hconj : (starRingEnd ℂ) (eulerHeadAnchor P s) * eulerHeadAnchor P s =
      ((‖eulerHeadAnchor P s‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj']
    push_cast
    ring
  rw [hconj] at hkey
  have hexp1 : Complex.exp (((anchorMirrorDefect P s : ℝ) : ℂ) * I) = 1 := by
    field_simp at hkey
    have hne : ((‖eulerHeadAnchor P s‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast pow_ne_zero 2 hAn.ne'
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact hkey.symm)
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp1
  refine ⟨n, ?_⟩
  have hI : ((anchorMirrorDefect P s : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi) := by
    have := hn
    rw [show (n : ℂ) * (2 * (Real.pi : ℂ) * I) = ((n : ℂ) * (2 * Real.pi)) * I by ring]
      at this
    exact mul_right_cancel₀ Complex.I_ne_zero this
  exact_mod_cast hI

/-! ### The mirror-angle law of the anchored incidence carrier -/

/-- **The anchored incidence value at the mirror point is the blind reversal rotated by
minus the defect**, up to the positive modulus ratio of the anchor values: with
`A = eulerHeadAnchor P` and `G = completedGN N`,
`ι(1−s̄) = (‖A(s)‖/‖A(1−s̄)‖)·exp(−defect·i)·conj(ι(s))`.  The departure of the anchored
pencil from the mirror-blind law is exactly the anchor's mirror defect. -/
theorem incidence_anchored_mirror {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {N : ℕ} {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    incidence (eulerHeadAnchor P) (completedGN N) (1 - (starRingEnd ℂ) s) =
      ((‖eulerHeadAnchor P s‖ / ‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖ : ℝ) : ℂ) *
        Complex.exp (-((anchorMirrorDefect P s : ℝ) : ℂ) * I) *
        (starRingEnd ℂ) (incidence (eulerHeadAnchor P) (completedGN N) s) := by
  have hms : 0 < (1 - (starRingEnd ℂ) s).re := by
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hA : eulerHeadAnchor P s ≠ 0 := eulerHeadAnchor_ne_zero hP h0
  have hAm : eulerHeadAnchor P (1 - (starRingEnd ℂ) s) ≠ 0 := eulerHeadAnchor_ne_zero hP hms
  have hAn : (0 : ℝ) < ‖eulerHeadAnchor P s‖ := norm_pos_iff.mpr hA
  have hAmn : (0 : ℝ) < ‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖ := norm_pos_iff.mpr hAm
  have hAc : (starRingEnd ℂ) (eulerHeadAnchor P s) ≠ 0 := star_ne_zero.mpr hA
  have hG := completedGN_lineReflection (N := N) h0 h1
  have hkey := eulerHeadAnchor_mul_mirror P s
  have hmc : eulerHeadAnchor P s * (starRingEnd ℂ) (eulerHeadAnchor P s) =
      ((‖eulerHeadAnchor P s‖ * ‖eulerHeadAnchor P s‖ : ℝ) : ℂ) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  have hexp' : Complex.exp (-((anchorMirrorDefect P s : ℝ) : ℂ) * I) *
      Complex.exp (((anchorMirrorDefect P s : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    rw [show -((anchorMirrorDefect P s : ℝ) : ℂ) * I +
        ((anchorMirrorDefect P s : ℝ) : ℂ) * I = 0 by ring]
    exact Complex.exp_zero
  set Rm := ‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖ with hRm_def
  set Rs := ‖eulerHeadAnchor P s‖ with hRs_def
  have hcoef : ((Rs / Rm : ℝ) : ℂ) * ((Rm * Rs : ℝ) : ℂ) = ((Rs * Rs : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [hAmn.ne']
  have hAms_eq : eulerHeadAnchor P (1 - (starRingEnd ℂ) s) =
      ((Rm * Rs : ℝ) : ℂ) *
        Complex.exp (((anchorMirrorDefect P s : ℝ) : ℂ) * I) / eulerHeadAnchor P s := by
    rw [eq_div_iff hA]
    exact hkey
  unfold incidence
  rw [hG, map_div₀, map_neg]
  rw [show ((Rs / Rm : ℝ) : ℂ) * Complex.exp (-((anchorMirrorDefect P s : ℝ) : ℂ) * I) *
      (-(starRingEnd ℂ) (completedGN N s) / (starRingEnd ℂ) (eulerHeadAnchor P s)) =
      ((Rs / Rm : ℝ) : ℂ) * Complex.exp (-((anchorMirrorDefect P s : ℝ) : ℂ) * I) *
        (-(starRingEnd ℂ) (completedGN N s)) / (starRingEnd ℂ) (eulerHeadAnchor P s)
    from by ring]
  rw [div_eq_div_iff hAm hAc, hAms_eq]
  rw [show ((Rs / Rm : ℝ) : ℂ) * Complex.exp (-((anchorMirrorDefect P s : ℝ) : ℂ) * I) *
      (-(starRingEnd ℂ) (completedGN N s)) *
      (((Rm * Rs : ℝ) : ℂ) * Complex.exp (((anchorMirrorDefect P s : ℝ) : ℂ) * I) /
        eulerHeadAnchor P s) =
      (((Rs / Rm : ℝ) : ℂ) * ((Rm * Rs : ℝ) : ℂ)) *
        (Complex.exp (-((anchorMirrorDefect P s : ℝ) : ℂ) * I) *
          Complex.exp (((anchorMirrorDefect P s : ℝ) : ℂ) * I)) *
        (-(starRingEnd ℂ) (completedGN N s)) / eulerHeadAnchor P s from by ring]
  rw [hcoef, hexp', mul_one, eq_div_iff hA]
  linear_combination (-(starRingEnd ℂ) (completedGN N s)) * hmc

/-- The orientation transfer in imaginary parts: the mirror orientation of the anchored
carrier is the defect-rotated blind reversal scaled by a positive factor. -/
theorem im_incidence_anchored_mirror {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {N : ℕ} {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    (incidence (eulerHeadAnchor P) (completedGN N) (1 - (starRingEnd ℂ) s)).im =
      (‖eulerHeadAnchor P s‖ / ‖eulerHeadAnchor P (1 - (starRingEnd ℂ) s)‖) *
        (Complex.exp (-((anchorMirrorDefect P s : ℝ) : ℂ) * I) *
          (starRingEnd ℂ) (incidence (eulerHeadAnchor P) (completedGN N) s)).im := by
  rw [incidence_anchored_mirror hP h0 h1, mul_assoc, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- **Defect angle alone does not determine mirror orientation.**  For any proposed
defect angle `d`, the rotated-conjugate imaginary coordinate can be assigned arbitrarily
by changing the source complex value.  Thus the meeting argument cannot use defect
reachability alone; it must also control the source incidence value that co-moves with
the same prime set. -/
theorem rotatedConj_im_can_be_assigned (d y : ℝ) :
    ∃ z : ℂ, z ≠ 0 ∧
      (Complex.exp (-((d : ℝ) : ℂ) * I) * (starRingEnd ℂ) z).im = y := by
  let w : ℂ := 1 + (y : ℂ) * I
  let z : ℂ := (starRingEnd ℂ) (Complex.exp (((d : ℝ) : ℂ) * I) * w)
  refine ⟨z, ?_, ?_⟩
  · have hw : w ≠ 0 := by
      intro hw0
      have hre : w.re = 0 := by
        rw [hw0]
        simp
      simp [w] at hre
    exact star_ne_zero.mpr (mul_ne_zero (Complex.exp_ne_zero (((d : ℝ) : ℂ) * I)) hw)
  · have hcancel : Complex.exp (-((d : ℝ) : ℂ) * I) *
        Complex.exp (((d : ℝ) : ℂ) * I) = 1 := by
      rw [← Complex.exp_add]
      rw [show -((d : ℝ) : ℂ) * I + ((d : ℝ) : ℂ) * I = 0 by ring]
      exact Complex.exp_zero
    calc
      (Complex.exp (-((d : ℝ) : ℂ) * I) * (starRingEnd ℂ) z).im
          = (Complex.exp (-((d : ℝ) : ℂ) * I) *
              (Complex.exp (((d : ℝ) : ℂ) * I) * w)).im := by
              simp [z]
      _ = ((Complex.exp (-((d : ℝ) : ℂ) * I) *
              Complex.exp (((d : ℝ) : ℂ) * I)) * w).im := by ring_nf
      _ = y := by
              rw [hcancel]
              simp [w]

/-! ### The defect bound on a ball in the strip -/

/-- **The defect budget on any ball inside the strip** — in particular on the isolating
annulus of a hypothetical off-line zero: if the ball at `ρ` of radius `R` keeps both the
point and its mirror at real part `≥ σ₀ > 0`, the defect is bounded by twice the
height-uniform tilt budget, independently of the centre's height. -/
theorem abs_anchorMirrorDefect_le_of_mem_ball {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {ρ s : ℂ} {R σ₀ : ℝ} (h0 : 0 < σ₀) (hs : s ∈ ball ρ R)
    (hlo : σ₀ + R ≤ ρ.re) (hhi : ρ.re ≤ 1 - σ₀ - R) :
    |anchorMirrorDefect P s| ≤ 2 * tiltBudget P σ₀ := by
  have hre : |s.re - ρ.re| ≤ dist s ρ := by
    rw [Complex.dist_eq]
    exact le_trans (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) le_rfl
  have hdist : dist s ρ < R := mem_ball.mp hs
  have hre1 : σ₀ ≤ s.re := by
    have := abs_lt.mp (lt_of_le_of_lt hre hdist)
    linarith
  have hre2 : σ₀ ≤ (1 - (starRingEnd ℂ) s).re := by
    rw [Complex.sub_re, Complex.one_re, Complex.conj_re]
    have := abs_lt.mp (lt_of_le_of_lt hre hdist)
    linarith
  unfold anchorMirrorDefect
  calc |anchorTilt P (1 - (starRingEnd ℂ) s) + anchorTilt P s|
      ≤ |anchorTilt P (1 - (starRingEnd ℂ) s)| + |anchorTilt P s| := abs_add_le _ _
    _ ≤ tiltBudget P σ₀ + tiltBudget P σ₀ :=
        add_le_add (abs_anchorTilt_le hP h0 hre2) (abs_anchorTilt_le hP h0 hre1)
    _ = 2 * tiltBudget P σ₀ := by ring

/-! ### The critical line: the anchor breaks the symmetry at almost every height -/

/-- The single-prime anchor. -/
private theorem eulerHeadAnchor_singleton (p : ℕ) (s : ℂ) :
    eulerHeadAnchor {p} s = 1 - (p : ℂ) ^ (-s) :=
  Finset.prod_singleton _ _

/-- **The single-prime anchor's imaginary part on the critical line** is the pure prime
oscillation `p^{−1/2}·sin(τ·log p)`. -/
private theorem eulerHeadAnchor_line_im {p : ℕ} (hp : 2 ≤ p) (τ : ℝ) :
    (eulerHeadAnchor {p} (stripPt (1/2) τ)).im =
      (p : ℝ) ^ (-(1/2 : ℝ)) * Real.sin (τ * Real.log p) := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast Nat.cast_ne_zero.mpr (by omega)
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [show ((p : ℕ) : ℂ) = (((p : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log hppos.le]
  rw [eulerHeadAnchor_singleton, Complex.cpow_def_of_ne_zero hpne, hlog]
  have hexp : ((Real.log p : ℝ) : ℂ) * (-stripPt (1/2) τ) =
      ((-(Real.log p) / 2 : ℝ) : ℂ) + ((-(τ * Real.log p) : ℝ) : ℂ) * I := by
    unfold stripPt
    push_cast
    ring
  rw [hexp, Complex.exp_add, ← Complex.ofReal_exp]
  rw [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
  rw [Real.sin_neg, Real.rpow_def_of_pos hppos]
  ring_nf

/-- **The anchor fails line-reflection equivariance at every height where
`sin(τ·log p) ≠ 0`** — the equivariance hypothesis of the mirror-blindness theorems is
violated by the anchor at all heights off a discrete set: the anchor is the symmetry
breaker of the anchored pencil. -/
theorem eulerHeadAnchor_not_lineReflection_on_line {p : ℕ} (hp : 2 ≤ p) {τ : ℝ}
    (hτ : Real.sin (τ * Real.log p) ≠ 0) :
    eulerHeadAnchor {p} (1 - (starRingEnd ℂ) (stripPt (1/2) τ)) ≠
      (starRingEnd ℂ) (eulerHeadAnchor {p} (stripPt (1/2) τ)) := by
  have hfix : (1 : ℂ) - (starRingEnd ℂ) (stripPt (1/2) τ) = stripPt (1/2) τ := by
    have h := stripPt_mirror (1/2) τ
    rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num] at h
    exact h.symm
  rw [hfix]
  intro h
  have him : (eulerHeadAnchor {p} (stripPt (1/2) τ)).im = 0 :=
    Complex.conj_eq_iff_im.mp h.symm
  rw [eulerHeadAnchor_line_im hp] at him
  have hppos : (0 : ℝ) < (p : ℝ) ^ (-(1/2 : ℝ)) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < p)) _
  rcases mul_eq_zero.mp him with h' | h'
  · exact absurd h' hppos.ne'
  · exact hτ h'

end RHTower
