import GaloisForLFunctions.RHTower.SuzukiXiFirstDefectJet
import GaloisForLFunctions.HTGeometry.FormInverseAntitone
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
# The Toeplitz `sech` wall and the hyperbolic parity budget

A common-Toeplitz energy form is invariant under midpoint reflection, and the two exponential
parity sources are exchanged by that reflection up to the scale `e^a`.  Hence the two source
energies satisfy `A = e^{2a} B` exactly, while Cauchy–Schwarz for the same positive form gives
`|D| ≤ e^a B`.  The Toeplitz Cayley scalar is therefore

`κ₀ = 2D/(A+B) = sech(a) · χ`,   `χ = D/(e^a B) ∈ [-1,1]`,

so `|κ₀| ≤ sech(a)` uniformly in the shift: an exponential wall, not a large-shift approximation.

A form contraction with normalized edge `r` moves the energy ratio by the factor `(1+r)/(1-r)`,
which in the Cayley coordinate is the Möbius addition `κ ≤ (κ₀+r)/(1+κ₀r)` — equivalently the
hyperbolic addition `artanh κ ≤ artanh κ₀ + artanh r`.  Reaching a target defect `κ_Ξ` therefore
forces the normalized edge to clear `(κ_Ξ - sech a)/(1 - κ_Ξ sech a)`, which tends to `κ_Ξ` as the
aperture grows.  With the unconditional `κ_Ξ > 77/85` this is the asymptotic wall.
-/

open Real Filter Topology

noncomputable section

namespace RHTower

/-! ## Cauchy–Schwarz for a real positive semidefinite form -/

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Cauchy–Schwarz for a symmetric positive semidefinite bilinear form.** -/
theorem sq_le_of_psd_bilinear {b : V → V → ℝ}
    (hsymm : ∀ x y, b x y = b y x)
    (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hsmul : ∀ (c : ℝ) (x y : V), b (c • x) y = c * b x y)
    (hpsd : ∀ x, 0 ≤ b x x) (x y : V) :
    b x y ^ (2 : ℕ) ≤ b x x * b y y := by
  have hadd₂ : ∀ p q r : V, b p (q + r) = b p q + b p r := by
    intro p q r
    rw [hsymm, hadd, hsymm q p, hsymm r p]
  have hsmul₂ : ∀ (c : ℝ) (p q : V), b p (c • q) = c * b p q := by
    intro c p q
    rw [hsymm, hsmul, hsymm q p]
  have hquad : ∀ t : ℝ, 0 ≤ t ^ (2 : ℕ) * b x x + 2 * t * b x y + b y y := by
    intro t
    have h := hpsd (t • x + y)
    rw [hadd, hsmul, hadd₂, hadd₂, hsmul₂, hsmul₂, hsymm y x] at h
    nlinarith [h]
  rcases eq_or_lt_of_le (hpsd x) with hzero | hpos
  · -- degenerate direction: the cross term must vanish
    have hxy : b x y = 0 := by
      by_contra hne
      have hval := hquad (-(b y y + 1) / (2 * b x y))
      rw [← hzero] at hval
      have h2 : (2 : ℝ) * (-(b y y + 1) / (2 * b x y)) * b x y = -(b y y + 1) := by
        field_simp
      rw [h2] at hval
      simp at hval
      linarith
    rw [hxy, ← hzero]
    simp
  · have hval := hquad (-(b x y) / b x x)
    have hne : b x x ≠ 0 := ne_of_gt hpos
    have hexp : (-(b x y) / b x x) ^ (2 : ℕ) * b x x + 2 * (-(b x y) / b x x) * b x y + b y y
        = b y y - b x y ^ (2 : ℕ) / b x x := by
      field_simp
      ring
    rw [hexp] at hval
    have h : b x y ^ (2 : ℕ) / b x x ≤ b y y := by linarith
    rw [div_le_iff₀ hpos] at h
    calc b x y ^ (2 : ℕ) ≤ b y y * b x x := h
      _ = b x x * b y y := mul_comm _ _

/-! ## The exact reflection identities -/

/-- **Midpoint reflection exchanges the exponential sources.**  The two source energies differ
exactly by `e^{2a}`. -/
theorem energy_of_reflected {b : V → V → ℝ} {J : V → V}
    (hsmul : ∀ (c : ℝ) (x y : V), b (c • x) y = c * b x y)
    (hsymm : ∀ x y, b x y = b y x)
    (hJ : ∀ x y, b (J x) (J y) = b x y)
    {u v : V} {a : ℝ} (huv : u = Real.exp a • J v) :
    b u u = Real.exp (2 * a) * b v v := by
  have hsmul₂ : ∀ (c : ℝ) (p q : V), b p (c • q) = c * b p q := by
    intro c p q
    rw [hsymm, hsmul, hsymm q p]
  rw [huv, hsmul, hsmul₂, hJ]
  rw [show Real.exp (2 * a) = Real.exp a * Real.exp a by
    rw [← Real.exp_add]; ring_nf]
  ring

/-- **The cross energy is bounded by the reflected source energy.** -/
theorem abs_cross_le_exp_mul {b : V → V → ℝ} {J : V → V}
    (hsymm : ∀ x y, b x y = b y x)
    (hadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hsmul : ∀ (c : ℝ) (x y : V), b (c • x) y = c * b x y)
    (hpsd : ∀ x, 0 ≤ b x x)
    (hJ : ∀ x y, b (J x) (J y) = b x y)
    {u v : V} {a : ℝ} (huv : u = Real.exp a • J v) :
    |b u v| ≤ Real.exp a * b v v := by
  have hcs := sq_le_of_psd_bilinear hsymm hadd hsmul hpsd (J v) v
  rw [hJ] at hcs
  have hb : 0 ≤ b v v := hpsd v
  have habs : |b (J v) v| ≤ b v v := by
    have hsq : |b (J v) v| ^ (2 : ℕ) ≤ (b v v) ^ (2 : ℕ) := by
      rw [sq_abs]
      nlinarith [hcs]
    exact le_of_pow_le_pow_left₀ (by norm_num) hb hsq
  rw [huv, hsmul, abs_mul, abs_of_pos (Real.exp_pos a)]
  exact mul_le_mul_of_nonneg_left habs (Real.exp_pos a).le

/-! ## The `sech` wall -/

/-- **`(235)`: the Toeplitz Cayley scalar is the reflection fidelity damped by `sech a`.** -/
theorem cayleyScalar_eq_sech_mul_fidelity {a A B D : ℝ} (hB : 0 < B)
    (hA : A = Real.exp (2 * a) * B) :
    2 * D / (A + B) = (1 / Real.cosh a) * (D / (Real.exp a * B)) := by
  have hexp : Real.exp (2 * a) = Real.exp a * Real.exp a := by
    rw [← Real.exp_add]; ring_nf
  have hepos : 0 < Real.exp a := Real.exp_pos a
  have hcosh : Real.cosh a = (Real.exp a + Real.exp (-a)) / 2 := Real.cosh_eq a
  have hinv : Real.exp (-a) = (Real.exp a)⁻¹ := Real.exp_neg a
  have hcpos : 0 < Real.cosh a := Real.cosh_pos a
  rw [hA, hexp, hcosh, hinv]
  field_simp

/-- **`(229)`: the uniform `sech` wall.** -/
theorem abs_cayleyScalar_le_sech {a A B D : ℝ} (hB : 0 < B)
    (hA : A = Real.exp (2 * a) * B) (hD : |D| ≤ Real.exp a * B) :
    |2 * D / (A + B)| ≤ 1 / Real.cosh a := by
  have hepos : 0 < Real.exp a := Real.exp_pos a
  have hcpos : 0 < Real.cosh a := Real.cosh_pos a
  rw [cayleyScalar_eq_sech_mul_fidelity hB hA, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.cosh a)]
  have hfid : |D / (Real.exp a * B)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.exp a * B), div_le_one (by positivity)]
    exact hD
  nlinarith [hfid, (by positivity : (0:ℝ) < 1 / Real.cosh a)]

/-! ## The hyperbolic parity budget -/

/-- **`(230)`: a form contraction with normalized edge `r` is Möbius addition in the Cayley
coordinate.** -/
theorem cayley_le_mobius {E O E₀ O₀ r : ℝ} (hE : 0 < E) (hO : 0 < O)
    (hE₀ : 0 < E₀) (hO₀ : 0 < O₀) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hratio : E / O ≤ (E₀ / O₀) * ((1 + r) / (1 - r))) :
    (E - O) / (E + O)
      ≤ ((E₀ - O₀) / (E₀ + O₀) + r) / (1 + ((E₀ - O₀) / (E₀ + O₀)) * r) := by
  set κ₀ : ℝ := (E₀ - O₀) / (E₀ + O₀) with hκ₀
  have hsum₀ : 0 < E₀ + O₀ := by linarith
  have hκ₀lt : |κ₀| < 1 := by
    rw [hκ₀, abs_div, abs_of_pos hsum₀, div_lt_one hsum₀]
    rcases le_or_gt E₀ O₀ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hden : 0 < 1 + κ₀ * r := by
    rcases abs_lt.mp hκ₀lt with ⟨hlow, -⟩
    nlinarith
  have hsum : 0 < E + O := by linarith
  have hEO : E / O ≤ ((1 + κ₀) * (1 + r)) / ((1 - κ₀) * (1 - r)) := by
    have hO₀' : O₀ ≠ 0 := ne_of_gt hO₀
    have hsum₀' : E₀ + O₀ ≠ 0 := ne_of_gt hsum₀
    have h1p : 1 + κ₀ = 2 * E₀ / (E₀ + O₀) := by
      rw [hκ₀]; field_simp; ring
    have h1m : 1 - κ₀ = 2 * O₀ / (E₀ + O₀) := by
      rw [hκ₀]; field_simp; ring
    have hval : E₀ / O₀ = (1 + κ₀) / (1 - κ₀) := by
      rw [h1p, h1m]
      field_simp
    rw [hval] at hratio
    calc E / O ≤ (1 + κ₀) / (1 - κ₀) * ((1 + r) / (1 - r)) := hratio
      _ = ((1 + κ₀) * (1 + r)) / ((1 - κ₀) * (1 - r)) := by
          rw [div_mul_div_comm]
  rcases abs_lt.mp hκ₀lt with ⟨hlow, hhigh⟩
  have h1mκ : 0 < 1 - κ₀ := by linarith
  have h1mr : 0 < 1 - r := by linarith
  rw [div_le_div_iff₀ hsum hden]
  rw [div_le_div_iff₀ hO (by positivity)] at hEO
  nlinarith [hEO, hsum, hden, h1mκ, h1mr, hO.le, hE.le]

/-- **`(231)`: Möbius addition is hyperbolic addition.** -/
theorem artanh_mobius {x y : ℝ} (hx : |x| < 1) (hy : |y| < 1) :
    Real.artanh ((x + y) / (1 + x * y)) = Real.artanh x + Real.artanh y := by
  rcases abs_lt.mp hx with ⟨hx1, hx2⟩
  rcases abs_lt.mp hy with ⟨hy1, hy2⟩
  have p1 : (0 : ℝ) < 1 + x := by linarith
  have p2 : (0 : ℝ) < 1 - x := by linarith
  have p3 : (0 : ℝ) < 1 + y := by linarith
  have p4 : (0 : ℝ) < 1 - y := by linarith
  have hden : (0 : ℝ) < 1 + x * y := by nlinarith
  have hden' : (1 : ℝ) + x * y ≠ 0 := ne_of_gt hden
  have hp2 : (1 : ℝ) - x ≠ 0 := ne_of_gt p2
  have hp4 : (1 : ℝ) - y ≠ 0 := ne_of_gt p4
  have hz : |(x + y) / (1 + x * y)| < 1 := by
    rw [abs_div, abs_of_pos hden, div_lt_one hden]
    rcases le_or_gt 0 (x + y) with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_neg h]; nlinarith
  rcases abs_lt.mp hz with ⟨hz1, hz2⟩
  rw [Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    Real.artanh_eq_half_log ⟨by linarith, by linarith⟩,
    Real.artanh_eq_half_log ⟨by linarith, by linarith⟩]
  have hkey : (1 + (x + y) / (1 + x * y)) / (1 - (x + y) / (1 + x * y))
      = ((1 + x) / (1 - x)) * ((1 + y) / (1 - y)) := by
    have hsub : (1 : ℝ) - (x + y) / (1 + x * y) = ((1 - x) * (1 - y)) / (1 + x * y) := by
      field_simp
      ring
    have hadd : (1 : ℝ) + (x + y) / (1 + x * y) = ((1 + x) * (1 + y)) / (1 + x * y) := by
      field_simp
      ring
    rw [hsub, hadd]
    field_simp
  rw [hkey, Real.log_mul (by positivity) (by positivity)]
  ring

/-- **`(232)`: reaching the target defect forces a normalized negative edge.** -/
theorem edge_lower_bound {κ κ₀ κXi r : ℝ}
    (hκ₀lt : |κ₀| < 1) (hκXi : |κXi| < 1)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hmob : κ ≤ (κ₀ + r) / (1 + κ₀ * r)) (htarget : κXi ≤ κ) :
    (κXi - κ₀) / (1 - κXi * κ₀) ≤ r := by
  rcases abs_lt.mp hκ₀lt with ⟨h1, h2⟩
  rcases abs_lt.mp hκXi with ⟨h3, h4⟩
  have hden : 0 < 1 + κ₀ * r := by nlinarith
  have hprod : 0 < 1 - κXi * κ₀ := by nlinarith
  have hchain : κXi ≤ (κ₀ + r) / (1 + κ₀ * r) := le_trans htarget hmob
  rw [le_div_iff₀ hden] at hchain
  rw [div_le_iff₀ hprod]
  nlinarith [hchain]

/-- The edge bound decreases in the Toeplitz scalar, so the `sech` wall is the binding case. -/
theorem edge_bound_antitone {κXi s t : ℝ} (hκXi0 : 0 < κXi) (hκXi1 : κXi < 1)
    (hs : |s| < 1) (ht : |t| < 1) (hst : s ≤ t) :
    (κXi - t) / (1 - κXi * t) ≤ (κXi - s) / (1 - κXi * s) := by
  rcases abs_lt.mp hs with ⟨hs1, hs2⟩
  rcases abs_lt.mp ht with ⟨ht1, ht2⟩
  have hds : 0 < 1 - κXi * s := by nlinarith
  have hdt : 0 < 1 - κXi * t := by nlinarith
  have hκsq : κXi ^ (2 : ℕ) < 1 := by nlinarith
  rw [div_le_div_iff₀ hdt hds]
  nlinarith [mul_nonneg (sub_nonneg.mpr hst) (by nlinarith : (0 : ℝ) ≤ 1 - κXi ^ (2 : ℕ))]

/-- **`(233)`: the asymptotic wall.**  As the aperture grows the `sech` damping vanishes, so the
edge bound tends to the target defect itself. -/
theorem tendsto_edge_bound_atTop (κXi : ℝ) :
    Tendsto (fun a : ℝ => (κXi - 1 / Real.cosh a) / (1 - κXi * (1 / Real.cosh a)))
      atTop (𝓝 κXi) := by
  have hsech : Tendsto (fun a : ℝ => 1 / Real.cosh a) atTop (𝓝 0) := by
    have hcosh : Tendsto Real.cosh atTop atTop := by
      have hle : ∀ a : ℝ, Real.exp a / 2 ≤ Real.cosh a := by
        intro a
        rw [Real.cosh_eq]
        have := (Real.exp_pos (-a)).le
        linarith
      exact tendsto_atTop_mono hle
        (Filter.Tendsto.atTop_div_const (by norm_num) Real.tendsto_exp_atTop)
    exact tendsto_const_nhds.div_atTop hcosh
  have hnum : Tendsto (fun a : ℝ => κXi - 1 / Real.cosh a) atTop (𝓝 κXi) := by
    simpa using tendsto_const_nhds.sub hsech
  have hden : Tendsto (fun a : ℝ => 1 - κXi * (1 / Real.cosh a)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hsech)
  have hlim := hnum.div hden one_ne_zero
  rw [div_one] at hlim
  exact hlim

end RHTower

namespace RHTower

open GaloisForLFunctions.HTGeometry

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## The form-contraction step -/

/-- **`(236)`–`(237)`: the normalized edge moves the energy ratio by `(1+r)/(1-r)`.**  The even
form is bounded below and the odd form above by the common Toeplitz form, so their represented
energies move in opposite directions.  No functional calculus is used: both bounds come from the
square completion behind `energy_le_of_form_le`. -/
theorem energyRatio_le_of_form_bounds
    {bE bO bC : V → V → ℝ} {wE wO wCE wCO : V} {m : ℝ}
    (hm1 : -1 < m) (hm2 : m < 1)
    (hCsymm : ∀ x y, bC x y = bC y x)
    (hCadd : ∀ x y z, bC (x + y) z = bC x z + bC y z)
    (hCsmul : ∀ (t : ℝ) (x y : V), bC (t • x) y = t * bC x y)
    (hCpsd : ∀ x, 0 ≤ bC x x)
    (hOsymm : ∀ x y, bO x y = bO y x)
    (hOadd : ∀ x y z, bO (x + y) z = bO x z + bO y z)
    (hOsmul : ∀ (t : ℝ) (x y : V), bO (t • x) y = t * bO x y)
    (hOpsd : ∀ x, 0 ≤ bO x x)
    (hrepE : ∀ x, bE wE x = bC wCE x)
    (hrepO : ∀ x, bO wO x = bC wCO x)
    (hlowE : ∀ x, (1 + m) * bC x x ≤ bE x x)
    (hhighO : ∀ x, bO x x ≤ (1 - m) * bC x x)
    (hCO : 0 < bC wCO wCO) (hCE : 0 ≤ bC wCE wCE) :
    bE wE wE / bO wO wO
      ≤ (bC wCE wCE / bC wCO wCO) * ((1 + max 0 (-m)) / (1 - max 0 (-m))) := by
  have h1m : (0 : ℝ) < 1 + m := by linarith
  have h1M : (0 : ℝ) < 1 - m := by linarith
  have hE : bE wE wE ≤ bC wCE wCE / (1 + m) :=
    energy_le_of_form_le h1m hCsymm hCadd hCsmul hCpsd hrepE hlowE
  have hOge : bC wCO wCO / (1 - m) ≤ bO wO wO :=
    le_energy_of_form_le h1M hOsymm hOadd hOsmul hOpsd hrepO hhighO
  set r : ℝ := max 0 (-m) with hr
  have hr0 : 0 ≤ r := le_max_left _ _
  have hr1 : r < 1 := max_lt (by norm_num) (by linarith)
  have hfactor : (1 - m) / (1 + m) ≤ (1 + r) / (1 - r) := by
    rcases le_or_gt 0 m with hpos | hneg
    · have hrm : r = 0 := by
        rw [hr, max_eq_left (by linarith)]
      rw [hrm]
      simp only [add_zero, sub_zero, div_one]
      rw [div_le_one h1m]
      linarith
    · have hrm : r = -m := by
        rw [hr, max_eq_right (by linarith)]
      rw [hrm, show (1 : ℝ) + -m = 1 - m by ring, show (1 : ℝ) - -m = 1 + m by ring]
  calc bE wE wE / bO wO wO
      ≤ (bC wCE wCE / (1 + m)) / (bC wCO wCO / (1 - m)) := by
        refine div_le_div₀ (by positivity) hE (by positivity) hOge
    _ = (bC wCE wCE / bC wCO wCO) * ((1 - m) / (1 + m)) := by
        field_simp
    _ ≤ (bC wCE wCE / bC wCO wCO) * ((1 + r) / (1 - r)) := by
        refine mul_le_mul_of_nonneg_left hfactor (by positivity)

end RHTower
