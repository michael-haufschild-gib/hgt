import GaloisForLFunctions.RHTower.HalfWeightTwistedThetaInversion

/-!
# The sign of the quadratic Gauss sum

For a prime `p`, `G(p) = Σ_{r mod p} e(r²/p)` (`gaussQuad`) is evaluated by comparing two exact
expansions of `θ(1/p + iε)` (Landsberg–Schaar):

* periodic Poisson summation mod `p` (`theta_one_div_p_A`):
  `(2p²ε)^{1/2} θ(1/p + iε) = Σ_n ĉ(n) e^{-πn²/(2p²ε)}` with `ĉ(0) = G(p)`;
* the Fricke transformation `θ(-1/(4v)) = (-2iv)^{1/2} θ(v)` at `w = -1/(4(1/p + iε)) = -p/4 + v`,
  the parity split `θ(-p/4 + v) = θ(4v) + e(-p/4)(θ(v) - θ(4v))`, and Fricke again at `v` and `4v`
  (`theta_one_div_p_B`, `sideA_eq`).

As `ε → 0⁺` the first side tends to `G(p)` (`tendsto_sideA`, using `‖θ₃(it) - 1‖ → 0`). The second tends
to `(ip/2)^{1/2}(1 + e(-p/4))`, which gives **`gaussQuad_eq`**. Hence **Gauss's theorem**:
`G(p) = √p` for `p ≡ 1 (mod 4)` (`gaussQuad_of_mod_four_eq_one`) and
`G(p) = i√p` for `p ≡ 3 (mod 4)` (`gaussQuad_of_mod_four_eq_three`).

With `#{x : x² = a} = (a/p) + 1`, the Gauss sum of the Legendre symbol is `G(p)`
(`gaussSum_legendre`), which fixes the root number `τ(χ)/√p ∈ {1, i}` of the real primitive
character of odd prime conductor.
-/

open Complex Filter Topology
open scoped Real

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

section GaussSign

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- `θ(-1/(4v)) = (-2iv)^{1/2} θ(v)`. -/
theorem theta_fricke {v : ℂ} (hv : 0 < v.im) :
    theta (-1 / (4 * v)) = (-2 * I * v) ^ (1 / 2 : ℂ) * theta v := by
  have h2 : 0 < (2 * v).im := by simp; linarith
  have h := jacobiTheta_neg_inv h2
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  unfold theta
  rw [show 2 * (-1 / (4 * v)) = -(2 * v)⁻¹ by field_simp; ring, h]
  congr 2
  ring

theorem cexp_two_pi_I_int (k : ℤ) : cexp (2 * π * I * k) = 1 := by
  rw [show (2 * π * I * k : ℂ) = k * (2 * π * I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- The odd part of `θ`: `Σ_m e((2m+1)²v) = θ(v) - θ(4v)`. -/
theorem tsum_odd_theta {v : ℂ} (hv : 0 < v.im) :
    ∑' m : ℤ, cexp (2 * π * I * (((m * 2 + 1 : ℤ)) : ℂ) ^ 2 * v) = theta v - theta (4 * v) := by
  have hs := summable_theta_terms hv
  have hsplit := tsum_int_split_residue (q := 2) hs
  rw [← theta_eq_tsum, Fin.sum_univ_two] at hsplit
  have h0 : ∑' m : ℤ, cexp (2 * π * I * (((m * (2 : ℕ) + ((0 : Fin 2) : ℕ) : ℤ)) : ℂ) ^ 2 * v) =
      theta (4 * v) := by
    rw [theta_eq_tsum]
    refine tsum_congr fun m => ?_
    congr 1; simp only [Fin.val_zero]; push_cast; ring
  rw [h0] at hsplit
  have h1 : ∑' m : ℤ, cexp (2 * π * I * (((m * (2 : ℕ) + ((1 : Fin 2) : ℕ) : ℤ)) : ℂ) ^ 2 * v) =
      ∑' m : ℤ, cexp (2 * π * I * (((m * 2 + 1 : ℤ)) : ℂ) ^ 2 * v) := by
    refine tsum_congr fun m => ?_
    simp only [Fin.val_one]
    push_cast
    ring_nf
  rw [h1] at hsplit
  rw [hsplit]; ring

/-- **`θ` at the quarter shift**: for odd `p`, `θ(-p/4 + v) = θ(4v) + e(-p/4)(θ(v) - θ(4v))`. -/
theorem theta_quarter_shift (p : ℕ) {v : ℂ} (hv : 0 < v.im) :
    theta (-(p : ℂ) / 4 + v) =
      theta (4 * v) + cexp (2 * π * I * (-(p : ℂ) / 4)) * (theta v - theta (4 * v)) := by
  have hv' : 0 < (-(p : ℂ) / 4 + v).im := by simp; exact hv
  have hs := summable_theta_terms hv'
  have hsplit := tsum_int_split_residue (q := 2) hs
  rw [← theta_eq_tsum, Fin.sum_univ_two] at hsplit
  have h0 : ∑' m : ℤ, cexp (2 * π * I * (((m * (2 : ℕ) + ((0 : Fin 2) : ℕ) : ℤ)) : ℂ) ^ 2 *
      (-(p : ℂ) / 4 + v)) = theta (4 * v) := by
    rw [theta_eq_tsum]
    refine tsum_congr fun m => ?_
    have e : 2 * π * I * (((m * (2 : ℕ) + ((0 : Fin 2) : ℕ) : ℤ)) : ℂ) ^ 2 * (-(p : ℂ) / 4 + v) =
        2 * π * I * (m : ℂ) ^ 2 * (4 * v) + 2 * π * I * ((-((p : ℤ) * m ^ 2) : ℤ) : ℂ) := by
      simp only [Fin.val_zero]; push_cast; ring
    rw [e, Complex.exp_add, cexp_two_pi_I_int, mul_one]
  have h1 : ∑' m : ℤ, cexp (2 * π * I * (((m * (2 : ℕ) + ((1 : Fin 2) : ℕ) : ℤ)) : ℂ) ^ 2 *
      (-(p : ℂ) / 4 + v)) = cexp (2 * π * I * (-(p : ℂ) / 4)) *
        ∑' m : ℤ, cexp (2 * π * I * (((m * 2 + 1 : ℤ)) : ℂ) ^ 2 * v) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun m => ?_
    have e : 2 * π * I * (((m * (2 : ℕ) + ((1 : Fin 2) : ℕ) : ℤ)) : ℂ) ^ 2 * (-(p : ℂ) / 4 + v) =
        2 * π * I * (-(p : ℂ) / 4) + 2 * π * I * (((m * 2 + 1 : ℤ)) : ℂ) ^ 2 * v +
          2 * π * I * ((-((p : ℤ) * (m ^ 2 + m)) : ℤ) : ℂ) := by
      simp only [Fin.val_one]; push_cast; ring
    rw [e, Complex.exp_add, Complex.exp_add, cexp_two_pi_I_int, mul_one]
  rw [h0, h1, tsum_odd_theta hv] at hsplit
  exact hsplit

variable (p : ℕ) [hp : Fact p.Prime]

/-- The Gauss-sum weights `ĉ(n) = Σ_{r mod p} e(r²/p) e(rn/p)`. -/
def gHat (n : ℤ) : ℂ :=
  ∑ r : Fin p, cexp (2 * π * I * (((r : ℕ) : ℤ) : ℂ) ^ 2 / p) * cexp (2 * π * I * ((r : ℕ) : ℂ) * n / p)

/-- The quadratic Gauss sum `G(p) = Σ_{r mod p} e(r²/p) = ĉ(0)`. -/
def gaussQuad : ℂ := ∑ r : Fin p, cexp (2 * π * I * (((r : ℕ) : ℤ) : ℂ) ^ 2 / p)

omit hp in
theorem gHat_zero : gHat p 0 = gaussQuad p := by
  unfold gHat gaussQuad
  refine Finset.sum_congr rfl fun r _ => ?_
  simp

/-- The periodic-inversion expansion: `θ(1/p + iε) = (2p²ε)^{-1/2} Σ_n ĉ(n) e^{-πn²/(2p²ε)}`. -/
theorem theta_one_div_p_A {ε : ℝ} (hε : 0 < ε) :
    theta (1 / p + I * ε) = 1 / ((2 * p ^ 2 * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
      ∑' n : ℤ, gHat p n * cexp (2 * π * I * (n : ℂ) ^ 2 * (-1 / (4 * (p : ℂ) ^ 2 * (I * ε)))) := by
  have hz : 0 < (I * (ε : ℂ)).im := by simp; exact hε
  have hc : ∀ n : ℤ, (fun n : ℤ => cexp (2 * π * I * (n : ℂ) ^ 2 / p)) (n + p) =
      (fun n : ℤ => cexp (2 * π * I * (n : ℂ) ^ 2 / p)) n := by
    intro n
    simp only
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [show 2 * π * I * (((n + p : ℤ)) : ℂ) ^ 2 / p = 2 * π * I * (n : ℂ) ^ 2 / p +
        2 * π * I * ((2 * n + p : ℤ) : ℂ) by push_cast; field_simp; ring,
      Complex.exp_add, cexp_two_pi_I_int, mul_one]
  have h := thetaPeriodic_inversion (q := p) (fun n : ℤ => cexp (2 * π * I * (n : ℂ) ^ 2 / p)) hc hz
  have hl : theta (1 / p + I * ε) = ∑' n : ℤ, (fun n : ℤ => cexp (2 * π * I * (n : ℂ) ^ 2 / p)) n *
      cexp (2 * π * I * (n : ℂ) ^ 2 * (I * ε)) := by
    rw [theta_eq_tsum]
    refine tsum_congr fun n => ?_
    simp only
    rw [← Complex.exp_add]
    congr 1; ring
  rw [hl, h]
  have e : (-2 * I * (p : ℂ) ^ 2 * (I * ε)) = ((2 * p ^ 2 * ε : ℝ) : ℂ) := by
    push_cast; ring_nf; rw [I_sq]; ring
  rw [e]
  rfl

/-- The point `v = w + p/4 = ip²ε/(4(1 + ipε))`, where `w = -1/(4(1/p + iε))`. -/
def vEps (ε : ℝ) : ℂ := I * (p : ℂ) ^ 2 * ε / (4 * (1 + I * p * ε))

omit hp in
theorem one_add_I_ne_zero (ε : ℝ) : (1 + I * (p : ℂ) * ε) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

omit hp in
theorem vEps_eq (ε : ℝ) : vEps p ε = (((p : ℝ) ^ 3 * ε ^ 2 / (4 * (1 + (p : ℝ) ^ 2 * ε ^ 2)) : ℝ) : ℂ) +
    (((p : ℝ) ^ 2 * ε / (4 * (1 + (p : ℝ) ^ 2 * ε ^ 2)) : ℝ) : ℂ) * I := by
  unfold vEps
  have h1 := one_add_I_ne_zero p ε
  have h2 : (1 + ((p : ℝ) : ℂ) ^ 2 * (ε : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + (p : ℝ) ^ 2 * ε ^ 2 := by positivity
    exact_mod_cast this.ne'
  push_cast at h2 ⊢
  have key : (I * (p : ℂ) ^ 2 * ε) * (1 + (p : ℂ) ^ 2 * ε ^ 2) =
      ((p : ℂ) ^ 3 * ε ^ 2 + (p : ℂ) ^ 2 * ε * I) * (1 + I * p * ε) := by
    ring_nf; rw [I_sq]; ring
  have e : (p : ℂ) ^ 3 * ε ^ 2 / (4 * (1 + (p : ℂ) ^ 2 * ε ^ 2)) +
      (p : ℂ) ^ 2 * ε / (4 * (1 + (p : ℂ) ^ 2 * ε ^ 2)) * I =
      ((p : ℂ) ^ 3 * ε ^ 2 + (p : ℂ) ^ 2 * ε * I) / (4 * (1 + (p : ℂ) ^ 2 * ε ^ 2)) := by ring
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  rw [e, div_eq_div_iff (mul_ne_zero h4 h1) (mul_ne_zero h4 h2)]
  linear_combination 4 * key

omit hp in
theorem vEps_im_pos {ε : ℝ} (hε : 0 < ε) (hp0 : 0 < p) : 0 < (vEps p ε).im := by
  rw [vEps_eq]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_zero, mul_one, zero_add, add_zero]
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  positivity

omit hp in
/-- `w = -1/(4(1/p + iε)) = -p/4 + v`. -/
theorem w_eq {ε : ℝ} (hp0 : 0 < p) :
    -1 / (4 * (1 / (p : ℂ) + I * ε)) = -(p : ℂ) / 4 + vEps p ε := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have h1 := one_add_I_ne_zero p ε
  have e : 1 / (p : ℂ) + I * ε = (1 + I * p * ε) / p := by field_simp
  rw [e]
  unfold vEps
  field_simp
  ring

theorem theta_fricke' {v : ℂ} (hv : 0 < v.im) :
    theta v = theta (-1 / (4 * v)) / (-2 * I * v) ^ (1 / 2 : ℂ) := by
  have hne : (-2 * I * v) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h
    have hv0 : v ≠ 0 := fun h' => by rw [h'] at hv; simp at hv
    exfalso; apply hv0
    have : (-2 * I) ≠ 0 := by simp
    exact (mul_eq_zero.1 h).resolve_left this
  rw [theta_fricke hv, mul_div_cancel_left₀ _ hne]

/-- The Fricke expansion: `θ(1/p + iε) = (-2iw)^{1/2} [θ(4v) + e(-p/4)(θ(v) - θ(4v))]`, with `θ(u)` at
`u = v, 4v` rewritten as `θ(-1/(4u))/(-2iu)^{1/2}`. -/
theorem theta_one_div_p_B {ε : ℝ} (hε : 0 < ε) :
    theta (1 / p + I * ε) = (-2 * I * (-1 / (4 * (1 / (p : ℂ) + I * ε)))) ^ (1 / 2 : ℂ) *
      (theta (-1 / (4 * (4 * vEps p ε))) / (-2 * I * (4 * vEps p ε)) ^ (1 / 2 : ℂ) +
        cexp (2 * π * I * (-(p : ℂ) / 4)) *
          (theta (-1 / (4 * vEps p ε)) / (-2 * I * vEps p ε) ^ (1 / 2 : ℂ) -
            theta (-1 / (4 * (4 * vEps p ε))) / (-2 * I * (4 * vEps p ε)) ^ (1 / 2 : ℂ))) := by
  have hp0 := hp.out.pos
  have hv := vEps_im_pos p hε hp0
  have h4v : 0 < (4 * vEps p ε).im := by simp; linarith
  set w : ℂ := -1 / (4 * (1 / (p : ℂ) + I * ε)) with hw
  have hwv : w = -(p : ℂ) / 4 + vEps p ε := w_eq p hp0
  have hwim : 0 < w.im := by rw [hwv]; simpa using hv
  have hz : 1 / (p : ℂ) + I * ε = -1 / (4 * w) := by
    have hz0 : 1 / (p : ℂ) + I * ε ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; linarith
    rw [hw]; field_simp
  rw [hz, theta_fricke hwim, hwv, theta_quarter_shift p hv, theta_fricke' hv, theta_fricke' h4v]

/-! ### The limit `ε → 0⁺` -/

omit hp in
theorem norm_gHat_le (n : ℤ) : ‖gHat p n‖ ≤ p := by
  unfold gHat
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ r : Fin p, ‖cexp (2 * π * I * (((r : ℕ) : ℤ) : ℂ) ^ 2 / p) *
      cexp (2 * π * I * ((r : ℕ) : ℂ) * n / p)‖ ≤ 1 := by
    intro r
    rw [norm_mul]
    have e1 : ‖cexp (2 * π * I * (((r : ℕ) : ℤ) : ℂ) ^ 2 / p)‖ = 1 := by
      rw [show 2 * π * I * (((r : ℕ) : ℤ) : ℂ) ^ 2 / p = ((2 * π * (r : ℕ) ^ 2 / p : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have e2 : ‖cexp (2 * π * I * ((r : ℕ) : ℂ) * n / p)‖ = 1 := by
      rw [show 2 * π * I * ((r : ℕ) : ℂ) * n / p = ((2 * π * (r : ℕ) * n / p : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [e1, e2, mul_one]
  calc ∑ r : Fin p, _ ≤ ∑ _r : Fin p, (1 : ℝ) := Finset.sum_le_sum fun r _ => h r
    _ = p := by simp

/-- The Gaussian weights of the periodic-inversion expansion. -/
theorem cexp_gauss_eps (n : ℤ) {ε : ℝ} (hε : 0 < ε) :
    cexp (2 * π * I * (n : ℂ) ^ 2 * (-1 / (4 * (p : ℂ) ^ 2 * (I * ε)))) =
      cexp (π * I * (n : ℂ) ^ 2 * (I * ((1 / (2 * p ^ 2 * ε) : ℝ) : ℂ))) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  congr 1
  push_cast
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- `jacobiTheta(it) = Σ_n e^{-πn²t}` written with the same summands. -/
theorem jacobiTheta_eq_tsum' (τ : ℂ) :
    jacobiTheta τ = ∑' n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * τ) := by
  unfold jacobiTheta
  rfl

theorem gauss_term_real (n : ℤ) (t : ℝ) :
    cexp (π * I * (n : ℂ) ^ 2 * (I * (t : ℂ))) = ((Real.exp (-π * n ^ 2 * t) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem summable_gauss_terms {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * (I * (t : ℂ))) := by
  have h := (hasSum_jacobiTheta₂_term 0 (show 0 < (I * (t : ℂ)).im by simp; exact ht)).summable
  refine h.congr fun n => ?_
  simp only [jacobiTheta₂_term]
  congr 1; ring

omit hp in
/-- `‖Σ_n ĉ(n) e^{-πn²t} - ĉ(0)‖ ≤ p ‖θ₃(it) - 1‖`. -/
theorem norm_gaussSum_sub_le {t : ℝ} (ht : 0 < t) :
    ‖∑' n : ℤ, gHat p n * cexp (π * I * (n : ℂ) ^ 2 * (I * (t : ℂ))) - gHat p 0‖ ≤
      p * ‖jacobiTheta (I * t) - 1‖ := by
  set E : ℤ → ℂ := fun n => cexp (π * I * (n : ℂ) ^ 2 * (I * (t : ℂ))) with hE
  set δ : ℤ → ℂ := fun n => if n = 0 then 1 else 0 with hδ
  have hEs : Summable E := summable_gauss_terms ht
  have hδs : Summable δ := summable_of_ne_finset_zero (s := {0}) fun n hn => by simp at hn; simp [hδ, hn]
  have hr : ∀ n, E n - δ n = ((Real.exp (-π * n ^ 2 * t) - if n = 0 then 1 else 0 : ℝ) : ℂ) := by
    intro n
    simp only [hE, hδ, gauss_term_real]
    split_ifs <;> push_cast <;> ring
  have hr0 : ∀ n : ℤ, 0 ≤ Real.exp (-π * n ^ 2 * t) - if n = 0 then 1 else 0 := by
    intro n
    split_ifs with h
    · subst h; simp
    · simp only [sub_zero]; positivity
  have hdiff : Summable fun n => E n - δ n := hEs.sub hδs
  have hRs : Summable fun n : ℤ => Real.exp (-π * n ^ 2 * t) - if n = 0 then 1 else 0 := by
    have := (Complex.summable_ofReal).1 (hdiff.congr hr)
    exact this
  have hG : ∑' n : ℤ, gHat p n * δ n = gHat p 0 := by
    simp only [hδ, mul_ite, mul_one, mul_zero]
    exact tsum_ite_eq 0 _
  have hgs : Summable fun n => gHat p n * E n :=
    Summable.of_norm_bounded (hEs.norm.mul_left (p : ℝ)) fun n => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (norm_gHat_le p n) (norm_nonneg _)
  have hgδ : Summable fun n => gHat p n * δ n :=
    Summable.of_norm_bounded (hδs.norm.mul_left (p : ℝ)) fun n => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_right (norm_gHat_le p n) (norm_nonneg _)
  have hsub : ∑' n : ℤ, gHat p n * E n - gHat p 0 = ∑' n : ℤ, gHat p n * (E n - δ n) := by
    rw [← hG, ← hgs.tsum_sub hgδ]
    exact tsum_congr fun n => by ring
  have hθ : jacobiTheta (I * t) - 1 = ((∑' n : ℤ, (Real.exp (-π * n ^ 2 * t) - if n = 0 then 1 else 0) : ℝ) : ℂ) := by
    rw [jacobiTheta_eq_tsum', Complex.ofReal_tsum]
    have h1 : ∑' n : ℤ, δ n = 1 := by simp only [hδ]; exact tsum_ite_eq 0 1
    rw [← h1, ← hEs.tsum_sub hδs]
    exact tsum_congr fun n => hr n
  rw [hsub, hθ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg hr0)]
  have hbound : ∀ n, ‖gHat p n * (E n - δ n)‖ ≤ p * (Real.exp (-π * n ^ 2 * t) - if n = 0 then 1 else 0) := by
    intro n
    rw [norm_mul, hr n, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 n)]
    exact mul_le_mul_of_nonneg_right (norm_gHat_le p n) (hr0 n)
  have hns : Summable fun n => ‖gHat p n * (E n - δ n)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound (hRs.mul_left (p : ℝ))
  refine (norm_tsum_le_tsum_norm hns).trans ?_
  rw [← tsum_mul_left]
  exact hns.tsum_le_tsum hbound (hRs.mul_left _)

/-- `θ(z) → 1` as `Im z → ∞`, uniformly in `Re z`. -/
theorem norm_theta_sub_one_le {z : ℂ} (hz : 0 < z.im) :
    ‖theta z - 1‖ ≤ 2 / (1 - Real.exp (-π * (2 * z.im))) * Real.exp (-π * (2 * z.im)) := by
  have h2 : 0 < (2 * z).im := by simp; linarith
  have := norm_jacobiTheta_sub_one_le h2
  unfold theta
  simpa using this

theorem tendsto_bound_atTop :
    Tendsto (fun y : ℝ => 2 / (1 - Real.exp (-π * (2 * y))) * Real.exp (-π * (2 * y))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun y : ℝ => Real.exp (-π * (2 * y))) atTop (𝓝 0) := by
    have : Tendsto (fun y : ℝ => -π * (2 * y)) atTop atBot := by
      have hc : (0 : ℝ) < 2 * π := by positivity
      have := (tendsto_id.const_mul_atTop hc)
      refine (tendsto_neg_atTop_atBot.comp this).congr fun y => ?_
      simp; ring
    exact Real.tendsto_exp_atBot.comp this
  have h2 : Tendsto (fun y : ℝ => 2 / (1 - Real.exp (-π * (2 * y)))) atTop (𝓝 (2 * (1 - 0)⁻¹)) :=
    (((tendsto_const_nhds.sub h1).inv₀ (by norm_num)).const_mul 2).congr fun y => by ring
  have := h2.mul h1
  simpa using this

/-- If `Im z(ε) → ∞` then `θ(z(ε)) → 1`. -/
theorem tendsto_theta_one {ι : Type*} {l : Filter ι} {z : ι → ℂ} (hz : Tendsto (fun i => (z i).im) l atTop) :
    Tendsto (fun i => theta (z i)) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb := tendsto_bound_atTop.comp hz
  refine squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) ?_ hb
  filter_upwards [hz.eventually_gt_atTop 0] with i hi
  exact norm_theta_sub_one_le hi

omit hp in
theorem arg_one_add_ne_pi (ε : ℝ) : (1 + I * (p : ℂ) * ε).arg ≠ π := by
  intro h
  rw [Complex.arg_eq_pi_iff] at h
  have := h.1
  simp at this
  linarith

omit hp in
theorem sqrt_cpow_real {a : ℝ} (ha : 0 ≤ a) : ((a : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt a : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow ha]
  push_cast; ring_nf

/-- `(2p²ε)^{1/2} / (-8iv)^{1/2} = (1 + ipε)^{1/2}`. -/
theorem ratio_one {ε : ℝ} (hε : 0 < ε) :
    ((2 * p ^ 2 * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) / (-2 * I * (4 * vEps p ε)) ^ (1 / 2 : ℂ) =
      (1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hc : (0 : ℝ) < 2 * p ^ 2 * ε := by positivity
  have h1 := one_add_I_ne_zero p ε
  have e : -2 * I * (4 * vEps p ε) = (1 + I * (p : ℂ) * ε)⁻¹ * ((2 * p ^ 2 * ε : ℝ) : ℂ) := by
    unfold vEps
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [e, cpow_mul_ofReal_pos (inv_ne_zero h1) hc, Complex.inv_cpow _ _ (arg_one_add_ne_pi p ε)]
  have hc0 : ((2 * p ^ 2 * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [sqrt_cpow_real hc.le]; exact_mod_cast (Real.sqrt_pos.2 hc).ne'
  have ha0 : (1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h h1
  field_simp

/-- `(2p²ε)^{1/2} / (-2iv)^{1/2} = 2 (1 + ipε)^{1/2}`. -/
theorem ratio_two {ε : ℝ} (hε : 0 < ε) :
    ((2 * p ^ 2 * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) / (-2 * I * vEps p ε) ^ (1 / 2 : ℂ) =
      2 * (1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hc : (0 : ℝ) < p ^ 2 * ε / 2 := by positivity
  have h1 := one_add_I_ne_zero p ε
  have e : -2 * I * vEps p ε = (1 + I * (p : ℂ) * ε)⁻¹ * ((p ^ 2 * ε / 2 : ℝ) : ℂ) := by
    unfold vEps
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have e2 : ((2 * p ^ 2 * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) = 2 * ((p ^ 2 * ε / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
    rw [sqrt_cpow_real (by positivity), sqrt_cpow_real hc.le]
    rw [show (2 * (p : ℝ) ^ 2 * ε) = 2 ^ 2 * (p ^ 2 * ε / 2) by ring, Real.sqrt_mul (by norm_num),
      Real.sqrt_sq (by norm_num)]
    push_cast; ring
  rw [e, e2, cpow_mul_ofReal_pos (inv_ne_zero h1) hc, Complex.inv_cpow _ _ (arg_one_add_ne_pi p ε)]
  have hc0 : ((p ^ 2 * ε / 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [sqrt_cpow_real hc.le]; exact_mod_cast (Real.sqrt_pos.2 hc).ne'
  have ha0 : (1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; push Not; intro h; exact absurd h h1
  field_simp

/-- The periodic-inversion side as a function of `ε`. -/
def sideA (ε : ℝ) : ℂ :=
  ∑' n : ℤ, gHat p n * cexp (2 * π * I * (n : ℂ) ^ 2 * (-1 / (4 * (p : ℂ) ^ 2 * (I * ε))))

/-- **The exact identity** for `ε > 0`: both expansions of `θ(1/p + iε)`, normalised by `(2p²ε)^{1/2}`. -/
theorem sideA_eq {ε : ℝ} (hε : 0 < ε) :
    sideA p ε = (-2 * I * (-1 / (4 * (1 / (p : ℂ) + I * ε)))) ^ (1 / 2 : ℂ) *
      ((1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ) * theta (-1 / (4 * (4 * vEps p ε))) +
        cexp (2 * π * I * (-(p : ℂ) / 4)) *
          (2 * (1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ) * theta (-1 / (4 * vEps p ε)) -
            (1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ) * theta (-1 / (4 * (4 * vEps p ε))))) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hc : (0 : ℝ) < 2 * p ^ 2 * ε := by positivity
  have hc0 : ((2 * p ^ 2 * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [sqrt_cpow_real hc.le]; exact_mod_cast (Real.sqrt_pos.2 hc).ne'
  have hA := theta_one_div_p_A p hε
  have hS : sideA p ε = ((2 * p ^ 2 * ε : ℝ) : ℂ) ^ (1 / 2 : ℂ) * theta (1 / p + I * ε) := by
    rw [hA, sideA]; field_simp
  rw [hS, theta_one_div_p_B p hε, ← ratio_two p hε, ← ratio_one p hε]
  ring

/-! ### The five limits -/

omit hp in
theorem tendsto_inv_scale {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => 1 / (a * ε)) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun ε : ℝ => a * ε) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => a * ε) (𝓝 0) (𝓝 (a * 0)) := tendsto_const_nhds.mul tendsto_id
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact mul_pos ha hε
  refine (tendsto_inv_nhdsGT_zero.comp h1).congr fun ε => ?_
  simp [one_div]

omit hp in
theorem im_neg_inv_four_vEps {ε : ℝ} (hε : 0 < ε) (hp0 : 0 < p) :
    (-1 / (4 * vEps p ε)).im = 1 / ((p : ℝ) ^ 2 * ε) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0.ne'
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h1 := one_add_I_ne_zero p ε
  have e : -1 / (4 * vEps p ε) = ((-1 / p : ℝ) : ℂ) + ((1 / ((p : ℝ) ^ 2 * ε) : ℝ) : ℂ) * I := by
    unfold vEps
    push_cast
    field_simp
    ring_nf
    rw [I_sq]
    ring
  rw [e]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]

theorem tendsto_T2 : Tendsto (fun ε : ℝ => theta (-1 / (4 * vEps p ε))) (𝓝[>] 0) (𝓝 1) := by
  have hp0 := hp.out.pos
  have hpR : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
  refine tendsto_theta_one ?_
  refine (tendsto_inv_scale hpR).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [im_neg_inv_four_vEps p hε hp0]

theorem tendsto_T1 : Tendsto (fun ε : ℝ => theta (-1 / (4 * (4 * vEps p ε)))) (𝓝[>] 0) (𝓝 1) := by
  have hp0 := hp.out.pos
  have hpR : (0 : ℝ) < 4 * (p : ℝ) ^ 2 := by positivity
  refine tendsto_theta_one ?_
  refine (tendsto_inv_scale hpR).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have e : -1 / (4 * (4 * vEps p ε)) = ((1 / 4 : ℝ) : ℂ) * (-1 / (4 * vEps p ε)) := by
    push_cast; ring
  rw [e, Complex.im_ofReal_mul, im_neg_inv_four_vEps p hε hp0]
  field_simp

theorem tendsto_sideA : Tendsto (sideA p) (𝓝[>] 0) (𝓝 (gaussQuad p)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have ha : (0 : ℝ) < 2 * p ^ 2 := by positivity
  have ht := tendsto_inv_scale ha
  -- `jacobiTheta(it) → 1`
  have hθ : Tendsto (fun ε : ℝ => jacobiTheta (I * ((1 / (2 * p ^ 2 * ε) : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 1) := by
    have h := tendsto_theta_one (l := 𝓝[>] (0 : ℝ))
      (z := fun ε : ℝ => ((1 / (2 * p ^ 2 * ε) / 2 : ℝ) : ℂ) * I) ?_
    · refine h.congr fun ε => ?_
      unfold theta; congr 1; push_cast; ring
    · have hh := ht.atTop_div_const (show (0 : ℝ) < 2 by norm_num)
      refine hh.congr fun ε => ?_
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_one, zero_mul, add_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun ε : ℝ => (p : ℝ) * ‖jacobiTheta (I * ((1 / (2 * p ^ 2 * ε) : ℝ) : ℂ)) - 1‖)
      (𝓝[>] 0) (𝓝 ((p : ℝ) * 0)) := by
    refine tendsto_const_nhds.mul ?_
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hθ)
    exact this
  rw [mul_zero] at hb
  refine squeeze_zero' (Eventually.of_forall fun ε => norm_nonneg _) ?_ hb
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have htε : (0 : ℝ) < 1 / (2 * p ^ 2 * ε) := by have : (0 : ℝ) < ε := hε; positivity
  have hsA : sideA p ε = ∑' n : ℤ, gHat p n * cexp (π * I * (n : ℂ) ^ 2 * (I * ((1 / (2 * p ^ 2 * ε) : ℝ) : ℂ))) := by
    unfold sideA
    refine tsum_congr fun n => ?_
    rw [cexp_gauss_eps p n hε]
  rw [hsA, ← gHat_zero]
  exact norm_gaussSum_sub_le p htε

theorem tendsto_W :
    Tendsto (fun ε : ℝ => (-2 * I * (-1 / (4 * (1 / (p : ℂ) + I * ε)))) ^ (1 / 2 : ℂ)) (𝓝[>] 0)
      (𝓝 ((I * p / 2) ^ (1 / 2 : ℂ))) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hg : Tendsto (fun ε : ℝ => -2 * I * (-1 / (4 * (1 / (p : ℂ) + I * ε)))) (𝓝 0) (𝓝 (I * p / 2)) := by
    have hc : ContinuousAt (fun ε : ℝ => -2 * I * (-1 / (4 * (1 / (p : ℂ) + I * ε)))) 0 := by
      refine ContinuousAt.mul continuousAt_const (ContinuousAt.div continuousAt_const ?_ ?_)
      · fun_prop
      · simp [hpC]
    have hv : (fun ε : ℝ => -2 * I * (-1 / (4 * (1 / (p : ℂ) + I * ε)))) 0 = I * p / 2 := by
      simp only [Complex.ofReal_zero, mul_zero, add_zero]
      field_simp
      ring
    rw [← hv]; exact hc.tendsto
  have hslit : I * (p : ℂ) / 2 ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; right
    simp; exact hp.out.ne_zero
  exact ((continuousAt_cpow_const hslit).tendsto.comp hg).mono_left nhdsWithin_le_nhds

omit hp in
theorem tendsto_R : Tendsto (fun ε : ℝ => (1 + I * (p : ℂ) * ε) ^ (1 / 2 : ℂ)) (𝓝[>] 0) (𝓝 1) := by
  have hg : Tendsto (fun ε : ℝ => 1 + I * (p : ℂ) * ε) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => 1 + I * (p : ℂ) * ε) 0 := by fun_prop
    simpa using this.tendsto
  have hslit : (1 : ℂ) ∈ Complex.slitPlane := Complex.one_mem_slitPlane
  have h := ((continuousAt_cpow_const (b := (1 / 2 : ℂ)) hslit).tendsto.comp hg).mono_left
    (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rw [Complex.one_cpow] at h
  exact h

/-- **Gauss's evaluation**: for a prime `p`, `Σ_{r mod p} e(r²/p) = (ip/2)^{1/2} (1 + e(-p/4))`. -/
theorem gaussQuad_eq : gaussQuad p = (I * p / 2) ^ (1 / 2 : ℂ) * (1 + cexp (2 * π * I * (-(p : ℂ) / 4))) := by
  have hR := tendsto_R p
  have hlim : Tendsto (sideA p) (𝓝[>] 0)
      (𝓝 ((I * p / 2) ^ (1 / 2 : ℂ) * (1 * 1 + cexp (2 * π * I * (-(p : ℂ) / 4)) * (2 * 1 * 1 - 1 * 1)))) := by
    have h := (tendsto_W p).mul ((hR.mul (tendsto_T1 p)).add
      ((tendsto_const_nhds (x := cexp (2 * π * I * (-(p : ℂ) / 4)))).mul
        (((tendsto_const_nhds (x := (2 : ℂ))).mul hR).mul (tendsto_T2 p) |>.sub (hR.mul (tendsto_T1 p)))))
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (sideA_eq p hε).symm
  have := tendsto_nhds_unique (tendsto_sideA p) hlim
  rw [this]; ring

theorem I_cpow_half : I ^ (1 / 2 : ℂ) = ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + I) := by
  rw [Complex.cpow_def_of_ne_zero I_ne_zero, Complex.log_I]
  rw [show ↑π / 2 * I * (1 / 2 : ℂ) = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; ring

theorem cexp_neg_quarter (k : ℕ) (r : ℕ) :
    cexp (2 * π * I * (-((4 * k + r : ℕ) : ℂ) / 4)) = cexp (2 * π * I * (-(r : ℂ) / 4)) := by
  rw [show 2 * π * I * (-((4 * k + r : ℕ) : ℂ) / 4) = 2 * π * I * (-(r : ℂ) / 4) +
      2 * π * I * ((-(k : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.exp_add, cexp_two_pi_I_int, mul_one]

theorem cexp_neg_one_quarter : cexp (2 * π * I * (-((1 : ℕ) : ℂ) / 4)) = -I := by
  rw [show 2 * π * I * (-((1 : ℕ) : ℂ) / 4) = ((-(π / 2) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem cexp_neg_three_quarter : cexp (2 * π * I * (-((3 : ℕ) : ℂ) / 4)) = I := by
  rw [show 2 * π * I * (-((3 : ℕ) : ℂ) / 4) = ((π / 2 : ℝ) : ℂ) * I + ((-1 : ℤ) : ℂ) * (2 * π * I) by
    push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

theorem I_mul_half_cpow : (I * p / 2) ^ (1 / 2 : ℂ) =
    ((Real.sqrt 2 / 2 : ℝ) : ℂ) * (1 + I) * ((Real.sqrt ((p : ℝ) / 2) : ℝ) : ℂ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) / 2 := by have := hp.out.pos; positivity
  rw [show I * (p : ℂ) / 2 = I * (((p : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    cpow_mul_ofReal_pos I_ne_zero hp0, I_cpow_half, sqrt_cpow_real hp0.le]

/-- **Gauss's sign of the quadratic Gauss sum**: for a prime `p ≡ 1 (mod 4)`,
`Σ_{r mod p} e(r²/p) = √p`. -/
theorem gaussQuad_of_mod_four_eq_one (h : p % 4 = 1) : gaussQuad p = (Real.sqrt p : ℂ) := by
  rw [gaussQuad_eq, I_mul_half_cpow]
  have hp4 : p = 4 * (p / 4) + 1 := by omega
  rw [hp4, cexp_neg_quarter, cexp_neg_one_quarter]
  rw [← hp4]
  have h2 : Real.sqrt 2 * Real.sqrt ((p : ℝ) / 2) = Real.sqrt p := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have h2C : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) / 2) : ℝ) : ℂ) = (Real.sqrt p : ℂ) := by
    exact_mod_cast h2
  push_cast
  linear_combination h2C - ((Real.sqrt 2 : ℂ) * (Real.sqrt ((p : ℝ) / 2) : ℂ)) / 2 * I_sq

/-- **Gauss's sign of the quadratic Gauss sum**: for a prime `p ≡ 3 (mod 4)`,
`Σ_{r mod p} e(r²/p) = i√p`. -/
theorem gaussQuad_of_mod_four_eq_three (h : p % 4 = 3) : gaussQuad p = I * (Real.sqrt p : ℂ) := by
  rw [gaussQuad_eq, I_mul_half_cpow]
  have hp4 : p = 4 * (p / 4) + 3 := by omega
  rw [hp4, cexp_neg_quarter, cexp_neg_three_quarter]
  rw [← hp4]
  have h2 : Real.sqrt 2 * Real.sqrt ((p : ℝ) / 2) = Real.sqrt p := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have h2C : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt ((p : ℝ) / 2) : ℝ) : ℂ) = (Real.sqrt p : ℂ) := by
    exact_mod_cast h2
  push_cast
  linear_combination I * h2C + ((Real.sqrt 2 : ℂ) * (Real.sqrt ((p : ℝ) / 2) : ℂ)) / 2 * I_sq

/-- The Legendre symbol mod `p` as a complex multiplicative character. -/
def legendreC : MulChar (ZMod p) ℂ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

theorem gaussQuad_eq_sum_zmod :
    gaussQuad p = ∑ x : ZMod p, ZMod.stdAddChar (x ^ 2) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  unfold gaussQuad
  let e : Fin p ≃ ZMod p :=
    { toFun := fun r => ((r : ℕ) : ZMod p)
      invFun := fun a => ⟨a.val, ZMod.val_lt a⟩
      left_inv := fun r => Fin.ext (ZMod.val_natCast_of_lt r.2)
      right_inv := fun a => ZMod.natCast_zmod_val a }
  refine Fintype.sum_equiv e _ _ fun r => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hk := Nat.mod_add_div ((r : ℕ) ^ 2) p
  have hv : ((((r : ℕ) : ZMod p) ^ 2).val : ℕ) = (r : ℕ) ^ 2 % p := by
    rw [← Nat.cast_pow, ZMod.val_natCast]
  rw [hv]
  obtain ⟨K, hK⟩ : ∃ K, K = (r : ℕ) ^ 2 / p := ⟨_, rfl⟩
  rw [← hK] at hk
  have hkC : (((r : ℕ) ^ 2 % p : ℕ) : ℂ) = ((r : ℕ) : ℂ) ^ 2 - p * K := by
    have := congrArg (fun n : ℕ => (n : ℂ)) hk
    push_cast at this
    linear_combination this
  rw [hkC, show 2 * (π : ℂ) * I * (((r : ℕ) : ℂ) ^ 2 - p * K) / p =
      2 * π * I * ((((r : ℕ) : ℤ) : ℂ) ^ 2 / p) + ((-K : ℤ) : ℂ) * (2 * π * I) by
    push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1; push_cast; ring

/-- **The Gauss sum of the Legendre symbol is the quadratic Gauss sum**: `τ((·/p)) = Σ_x e(x²/p)`. -/
theorem gaussSum_legendre (hp2 : p ≠ 2) : gaussSum (legendreC p) ZMod.stdAddChar = gaussQuad p := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  classical
  rw [gaussQuad_eq_sum_zmod]
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hψ : ZMod.stdAddChar (N := p) ≠ 1 := by
    have := ZMod.isPrimitive_stdAddChar p (one_ne_zero (α := ZMod p))
    simpa using this
  -- `Σ_x ψ(x²) = Σ_a #{x² = a} ψ(a)`
  have h1 : ∑ x : ZMod p, ZMod.stdAddChar (x ^ 2) =
      ∑ a : ZMod p, (((Finset.univ.filter fun x : ZMod p => x ^ 2 = a).card : ℕ) : ℂ) *
        ZMod.stdAddChar a := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x : ZMod p => x ^ 2)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [(Finset.mem_filter.1 hx).2]; simp
  rw [h1]
  have h2 : ∀ a : ZMod p, (((Finset.univ.filter fun x : ZMod p => x ^ 2 = a).card : ℕ) : ℂ) =
      legendreC p a + 1 := by
    intro a
    have := quadraticChar_card_sqrts hchar a
    unfold legendreC
    rw [MulChar.ringHomComp_apply]
    have e : (Finset.univ.filter fun x : ZMod p => x ^ 2 = a) = {x | x ^ 2 = a}.toFinset := by
      ext x; simp
    rw [e]
    have h := congrArg (fun z : ℤ => (z : ℂ)) this
    push_cast at h
    rw [h]
    rfl
  simp_rw [h2, add_mul, one_mul, Finset.sum_add_distrib, AddChar.sum_eq_zero_of_ne_one hψ, add_zero]
  rfl

end GaussSign

end

end GaloisForLFunctions.RHTower.HalfWeight
