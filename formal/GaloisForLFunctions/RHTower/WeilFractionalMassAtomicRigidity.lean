import GaloisForLFunctions.RHTower.WeilIntegerMassAtomicRigidity
import GaloisForLFunctions.RHTower.HamburgerTwistedCriticalLine

/-!
# Finitely many non-integer spectral masses force `Λ` and the Riemann hypothesis

Let `Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`, and suppose that on `Re s > 1`

`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s} = 2(s−½) Σ_j m_j/((s−½)² + t_j²)
  + Σ_{k<J} c_k · 2(s−½)/((s−½)² + u_k²)`,

with integer masses `m_j` at ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`) and finitely many real masses
`c_k ≥ 0` at ordinates `u_k ≥ 1`.  The right side is a Herglotz function whose boundary measure is
atomic with integer masses outside a bounded set.

**Theorem** (`fractional_mass_rigidity`).  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann
hypothesis holds.  The real masses `c_k` may be irrational.

**Proof.**
* The integer part exponentiates to the symmetric entire function `Q` of
  `IntegerMassRigidity.atomQ`.  Each real atom exponentiates to
  `((s − ½ + iu)/u)^c ((s − ½ − iu)/u)^c`, a branch of `(1 + (s−½)²/u²)^c` that is holomorphic on
  `Re s > ½` and continuous on `Re s ≥ ½`, because both bases lie in the closed right half-plane.
  So `G(s) = s(s−1)Γ_ℝ(s) exp(Σ lam(n)n^{-s}/log n)` equals `K Q R` on `Re s > 1`, where `R` is the
  product of these factors.
* On the critical line above every `u_k` both bases are positive multiples of `i`, so
  `R(½ + iy) = |R| e^{iπ C}` with `C = Σ c_k`.  Since `R(s̄) = conj R(s)` and `Q(1−s) = Q(s)`,
  `Ĝ(1 − s) = κ Ĝ(s)` with `κ = e^{−2πiC}` on the upper part of the line and `κ⁻¹` on the lower part.
* `Re Φ ≥ 0` gives horizontal monotonicity of `|Ĝ|` and, with Stirling at `σ = 2`, the decay and the
  polynomial bounds required by the twisted Hamburger theorem
  (`HamburgerTwisted.coeff_eq_of_critical_line_twisted_defect`).  It makes the coefficients of
  `exp(Σ lam(n)n^{-s}/log n)` constant, so this series is `ζ` and `lam = Λ`.
* Then `KQR = s(s−1)Λ(s)` on `Re s > ½`, and `QR` has no zero off the critical line.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace FractionalMassRigidity

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity

noncomputable section

/-! ### The real-mass factor -/

/-- A point of the closed right half-plane other than `0` lies in the slit plane. -/
theorem mem_slitPlane_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) (h0 : w ≠ 0) : w ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  rcases eq_or_lt_of_le hw with h | h
  · right
    intro him
    exact h0 (Complex.ext (by simp [← h]) (by simp [him]))
  · exact Or.inl h

/-- The argument of a point of the closed right half-plane is not `π`. -/
theorem arg_ne_pi_of_re_nonneg {w : ℂ} (hw : 0 ≤ w.re) : w.arg ≠ Real.pi := by
  intro h
  have h1 := Complex.abs_arg_le_pi_div_two_iff.mpr hw
  rw [h, abs_of_pos Real.pi_pos] at h1
  linarith [Real.pi_pos]

/-- The bases `(s − ½ ± iu)/u`. -/
def fracBase (σ u : ℝ) (s : ℂ) : ℂ := (s - 1 / 2 + σ * I) / u

theorem fracBase_re (σ u : ℝ) (s : ℂ) :
    (fracBase σ u s).re = (s.re - 1 / 2) / u := by
  unfold fracBase
  rw [Complex.div_ofReal_re]
  simp

theorem fracBase_re_nonneg {σ u : ℝ} (hu : 0 < u) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    0 ≤ (fracBase σ u s).re := by
  rw [fracBase_re]; exact div_nonneg (by linarith) hu.le

theorem fracBase_ne_zero {σ u : ℝ} (hu : 0 < u) {s : ℂ} (hs : s ≠ 1 / 2 - σ * I) :
    fracBase σ u s ≠ 0 := by
  unfold fracBase
  refine div_ne_zero ?_ (by exact_mod_cast hu.ne')
  intro h
  exact hs (by linear_combination h)

/-- One real-mass factor `((s − ½ + iu)/u)^c ((s − ½ − iu)/u)^c`. -/
def fracPair (c u : ℝ) (s : ℂ) : ℂ := fracBase u u s ^ (c : ℂ) * fracBase (-u) u s ^ (c : ℂ)

/-- The product of the real-mass factors. -/
def fracProd {J : ℕ} (c u : Fin J → ℝ) (s : ℂ) : ℂ := ∏ k, fracPair (c k) (u k) s

/-- The real-mass pair term `c · 2(s − ½)/((s − ½)² + u²)`. -/
def fracTerm (c u : ℝ) (s : ℂ) : ℂ := (c : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u : ℂ) ^ 2))

theorem hasDerivAt_fracBase_cpow {σ u c : ℝ} (hu : 0 < u) {s : ℂ}
    (hmem : fracBase σ u s ∈ slitPlane) :
    HasDerivAt (fun z => fracBase σ u z ^ (c : ℂ))
      ((c : ℂ) * fracBase σ u s ^ (c : ℂ) / (s - 1 / 2 + σ * I)) s := by
  have hb : HasDerivAt (fracBase σ u) (1 / (u : ℂ)) s := by
    unfold fracBase
    have := ((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).add_const ((σ : ℂ) * I)
    simpa [div_eq_mul_inv] using this.mul_const ((u : ℂ)⁻¹)
  have h := hb.cpow_const (c := (c : ℂ)) hmem
  have hne : fracBase σ u s ≠ 0 := slitPlane_ne_zero hmem
  have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hlin : s - 1 / 2 + σ * I ≠ 0 := by
    intro h0; apply hne; unfold fracBase; rw [h0, zero_div]
  refine h.congr_deriv ?_
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  have hb' : fracBase σ u s * u = s - 1 / 2 + σ * I := by
    unfold fracBase; field_simp
  rw [← hb']
  field_simp

/-- **The logarithmic derivative of one real-mass factor** on `Re s > ½`. -/
theorem hasDerivAt_fracPair {c u : ℝ} (hu : 0 < u) {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (fracPair c u) (fracPair c u s * fracTerm c u s) s := by
  have hre1 : 0 < (fracBase u u s).re := by rw [fracBase_re]; exact div_pos (by linarith) hu
  have hre2 : 0 < (fracBase (-u) u s).re := by
    rw [fracBase_re]; exact div_pos (by linarith) hu
  have h1 := hasDerivAt_fracBase_cpow (c := c) hu (mem_slitPlane_of_re_nonneg hre1.le
    (fun h => by rw [h] at hre1; simp at hre1))
  have h2 := hasDerivAt_fracBase_cpow (c := c) hu (mem_slitPlane_of_re_nonneg hre2.le
    (fun h => by rw [h] at hre2; simp at hre2))
  have hl1 : s - 1 / 2 + u * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hl2 : s - 1 / 2 + ((-u : ℝ) : ℂ) * I ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hprod := h1.mul h2
  refine hprod.congr_deriv ?_
  unfold fracPair fracTerm
  have hden : (s - 1 / 2) ^ 2 + (u : ℂ) ^ 2 =
      (s - 1 / 2 + u * I) * (s - 1 / 2 + ((-u : ℝ) : ℂ) * I) := by
    push_cast; ring_nf; rw [I_sq]; ring
  have hsum : 2 * (s - 1 / 2) = (s - 1 / 2 + u * I) + (s - 1 / 2 + ((-u : ℝ) : ℂ) * I) := by
    push_cast; ring
  rw [hden, hsum]
  set l1 := s - 1 / 2 + u * I with hl1d
  set l2 := s - 1 / 2 + ((-u : ℝ) : ℂ) * I with hl2d
  have key : (l1 + l2) / (l1 * l2) = 1 / l1 + 1 / l2 := by
    field_simp; ring
  rw [key]
  ring

theorem fracPair_ne_zero {c u : ℝ} (hu : 0 < u) {s : ℂ} (hs : 1 / 2 < s.re) :
    fracPair c u s ≠ 0 := by
  have hre1 : 0 < (fracBase u u s).re := by rw [fracBase_re]; exact div_pos (by linarith) hu
  have hre2 : 0 < (fracBase (-u) u s).re := by
    rw [fracBase_re]; exact div_pos (by linarith) hu
  unfold fracPair
  refine mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl ?_))
    (Complex.cpow_ne_zero_iff.mpr (Or.inl ?_))
  · intro h; rw [h] at hre1; simp at hre1
  · intro h; rw [h] at hre2; simp at hre2

/-- `w ↦ w^c` is continuous at every point of the closed right half-plane when `c ≥ 0`. -/
theorem continuousAt_cpow_ofReal_of_re_nonneg {c : ℝ} (hc : 0 ≤ c) {w : ℂ} (hw : 0 ≤ w.re) :
    ContinuousAt (fun z : ℂ => z ^ (c : ℂ)) w := by
  rcases eq_or_ne w 0 with h0 | h0
  · subst h0
    rcases eq_or_lt_of_le hc with hc0 | hcpos
    · subst hc0
      simp only [ofReal_zero, cpow_zero]
      exact continuousAt_const
    · have h := continuousAt_cpow_zero_of_re_pos (z := (c : ℂ)) (by simpa using hcpos)
      exact ContinuousAt.comp (g := fun x : ℂ × ℂ => x.1 ^ x.2) (f := fun z : ℂ => (z, (c : ℂ)))
        h (by fun_prop)
  · exact continuousAt_cpow_const (mem_slitPlane_of_re_nonneg hw h0)

theorem continuousAt_fracPair {c u : ℝ} (hc : 0 ≤ c) (hu : 0 < u) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : ContinuousAt (fracPair c u) s := by
  have hb : ∀ σ : ℝ, Continuous (fracBase σ u) := fun σ => by unfold fracBase; fun_prop
  unfold fracPair
  exact ((continuousAt_cpow_ofReal_of_re_nonneg hc (fracBase_re_nonneg hu hs)).comp
    (hb u).continuousAt).mul
    ((continuousAt_cpow_ofReal_of_re_nonneg hc (fracBase_re_nonneg hu hs)).comp
      (hb (-u)).continuousAt)

/-- **Reality of the real-mass factor:** `R(s̄) = conj R(s)` on `Re s ≥ ½`. -/
theorem fracPair_conj {c u : ℝ} (hu : 0 < u) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    fracPair c u (starRingEnd ℂ s) = starRingEnd ℂ (fracPair c u s) := by
  have hb1 : fracBase u u (starRingEnd ℂ s) = starRingEnd ℂ (fracBase (-u) u s) := by
    apply Complex.ext <;> simp [fracBase, Complex.div_ofReal_re, Complex.div_ofReal_im]
  have hb2 : fracBase (-u) u (starRingEnd ℂ s) = starRingEnd ℂ (fracBase u u s) := by
    apply Complex.ext <;> simp [fracBase, Complex.div_ofReal_re, Complex.div_ofReal_im]
  have ha1 := arg_ne_pi_of_re_nonneg (fracBase_re_nonneg (σ := u) hu hs)
  have ha2 := arg_ne_pi_of_re_nonneg (fracBase_re_nonneg (σ := -u) hu hs)
  unfold fracPair
  rw [hb1, hb2, Complex.conj_cpow _ _ ha2, Complex.conj_cpow _ _ ha1, Complex.conj_ofReal,
    map_mul]
  ring

/-- `(i a)^c = a^c e^{iπc/2}` for `a > 0`. -/
theorem cpow_I_mul_ofReal {a : ℝ} (ha : 0 < a) (c : ℝ) :
    (I * (a : ℂ)) ^ (c : ℂ) = ((a ^ c : ℝ) : ℂ) * Complex.exp (((Real.pi * c / 2 : ℝ) : ℂ) * I) := by
  have hne : I * (a : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast ha.ne')
  have hlog : Complex.log (I * (a : ℂ)) = (Real.log a : ℂ) + ((Real.pi / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [Complex.log_re]; simp [abs_of_pos ha]
    · rw [Complex.log_im]
      have : (I * (a : ℂ)).arg = Real.pi / 2 :=
        Complex.arg_eq_pi_div_two_iff.mpr ⟨by simp, by simp [ha]⟩
      rw [this]; simp
  rw [Complex.cpow_def_of_ne_zero hne, hlog, Real.rpow_def_of_pos ha, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- **The phase of one real-mass factor above its atom.**  For `y > u > 0`,
`conj R(½ + iy) = e^{−2πic} R(½ + iy)`. -/
theorem conj_fracPair_of_gt {c u : ℝ} (hu : 0 < u) {y : ℝ} (hy : u < y) :
    starRingEnd ℂ (fracPair c u (1 / 2 + y * I)) =
      Complex.exp (-(2 * Real.pi * c : ℝ) * I) * fracPair c u (1 / 2 + y * I) := by
  have hb1 : fracBase u u (1 / 2 + y * I) = I * (((y + u) / u : ℝ) : ℂ) := by
    unfold fracBase; push_cast; field_simp; ring
  have hb2 : fracBase (-u) u (1 / 2 + y * I) = I * (((y - u) / u : ℝ) : ℂ) := by
    unfold fracBase; push_cast; field_simp; ring
  have hp1 : 0 < (y + u) / u := div_pos (by linarith) hu
  have hp2 : 0 < (y - u) / u := div_pos (by linarith) hu
  unfold fracPair
  rw [hb1, hb2, cpow_I_mul_ofReal hp1, cpow_I_mul_ofReal hp2]
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  set A : ℂ := ((((y + u) / u) ^ c : ℝ) : ℂ)
  set B : ℂ := ((((y - u) / u) ^ c : ℝ) : ℂ)
  set θ : ℂ := ((Real.pi * c / 2 : ℝ) : ℂ) with hθ
  have key : Complex.exp (θ * -I) * Complex.exp (θ * -I) =
      Complex.exp (-((2 * Real.pi * c : ℝ) : ℂ) * I) *
        (Complex.exp (θ * I) * Complex.exp (θ * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hθ]; push_cast; ring
  linear_combination (A * B) * key

/-! ### The product of the real-mass factors -/

theorem hasDerivAt_fracProd {J : ℕ} {c u : Fin J → ℝ} (hu : ∀ k, 0 < u k) {s : ℂ}
    (hs : 1 / 2 < s.re) :
    HasDerivAt (fracProd c u) (fracProd c u s * ∑ k, fracTerm (c k) (u k) s) s := by
  classical
  have h := HasDerivAt.finsetProd (u := Finset.univ) (f := fun k => fracPair (c k) (u k))
    (f' := fun k => fracPair (c k) (u k) s * fracTerm (c k) (u k) s) (x := s)
    (fun k _ => hasDerivAt_fracPair (hu k) hs)
  have hfun : (∏ k ∈ (Finset.univ : Finset (Fin J)), fun z => fracPair (c k) (u k) z) =
      fracProd c u := by
    funext z; rw [Finset.prod_apply]; rfl
  rw [hfun] at h
  refine h.congr_deriv ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_mul]
  unfold fracProd
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  ring

theorem fracProd_ne_zero {J : ℕ} {c u : Fin J → ℝ} (hu : ∀ k, 0 < u k) {s : ℂ}
    (hs : 1 / 2 < s.re) : fracProd c u s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun k _ => fracPair_ne_zero (hu k) hs

theorem continuousAt_fracProd {J : ℕ} {c u : Fin J → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hu : ∀ k, 0 < u k) {s : ℂ} (hs : 1 / 2 ≤ s.re) : ContinuousAt (fracProd c u) s := by
  unfold fracProd
  exact tendsto_finsetProd _ fun k _ => continuousAt_fracPair (hc k) (hu k) hs

theorem fracProd_conj {J : ℕ} {c u : Fin J → ℝ} (hu : ∀ k, 0 < u k) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) : fracProd c u (starRingEnd ℂ s) = starRingEnd ℂ (fracProd c u s) := by
  unfold fracProd
  rw [map_prod]
  exact Finset.prod_congr rfl fun k _ => fracPair_conj (hu k) hs

/-- **The phase of the real-mass product above all its atoms.**
`conj R(½ + iy) = e^{−2πiC} R(½ + iy)` with `C = Σ c_k`, for `y > u_k` for every `k`. -/
theorem conj_fracProd_of_gt {J : ℕ} {c u : Fin J → ℝ} (hu : ∀ k, 0 < u k) {y : ℝ}
    (hy : ∀ k, u k < y) :
    starRingEnd ℂ (fracProd c u (1 / 2 + y * I)) =
      Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I) * fracProd c u (1 / 2 + y * I) := by
  unfold fracProd
  rw [map_prod, Finset.prod_congr rfl fun k _ => conj_fracPair_of_gt (c := c k) (hu k) (hy k),
    Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 2
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.sum_mul]

/-- The same phase law below all the atoms: `conj R(½ − iy) = e^{2πiC} R(½ − iy)`. -/
theorem conj_fracProd_of_lt {J : ℕ} {c u : Fin J → ℝ} (hu : ∀ k, 0 < u k) {y : ℝ}
    (hy : ∀ k, u k < y) :
    starRingEnd ℂ (fracProd c u (1 / 2 - y * I)) =
      (Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I))⁻¹ *
        fracProd c u (1 / 2 - y * I) := by
  have hs : (1 / 2 : ℝ) ≤ ((1 / 2 : ℂ) + y * I).re := by simp
  have hconj : (1 / 2 : ℂ) - y * I = starRingEnd ℂ ((1 / 2 : ℂ) + y * I) := by
    apply Complex.ext <;> simp
  have h1 := conj_fracProd_of_gt (c := c) hu hy
  set κ := Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I)
  have hκ : κ ≠ 0 := Complex.exp_ne_zero _
  rw [hconj, fracProd_conj hu hs, Complex.conj_conj, h1]
  field_simp

/-! ### A lower bound for `Γ_ℝ` on the critical line -/

/-- `‖sin z‖ ≤ e^{|Im z|}`. -/
theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h : Complex.sin z = (Complex.exp (-z * I) - Complex.exp (z * I)) * I / 2 := rfl
  rw [h, norm_div, norm_mul, norm_I, mul_one, Complex.norm_ofNat]
  have h1 : ‖Complex.exp (-z * I) - Complex.exp (z * I)‖ ≤ Real.exp z.im + Real.exp (-z.im) := by
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 2 <;> simp
  have h2 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have h3 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [div_le_iff₀ two_pos]
  linarith

/-- **Lower bound for `Γ_ℝ` on the critical line.**
`c e^{−π|v|/4} ≤ (1 + |v|)^M ‖Γ_ℝ(½ + iv)‖`. -/
theorem exists_lower_bound_Gammaℝ_half_line :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ, ∀ v : ℝ,
      c * Real.exp (-(Real.pi * |v| / 4)) ≤ (1 + |v|) ^ M * ‖Complex.Gammaℝ (1 / 2 + v * I)‖ := by
  obtain ⟨Cs, N, hCs, hs⟩ := exists_sharp_bound_norm_Gamma_strip (3 / 4) (3 / 4)
  have hcont : Continuous fun v : ℝ => Complex.Gamma (3 / 4 - ((v / 2 : ℝ) : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun v => ?_
    refine ContinuousAt.comp (g := Complex.Gamma) (f := fun v : ℝ => 3 / 4 - ((v / 2 : ℝ) : ℂ) * I)
      (Complex.continuousAt_Gamma _ fun m hm => ?_) (by fun_prop)
    have h := congrArg Complex.re hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp at h
    linarith
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-2 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hcont.continuousOn
  set C' : ℝ := max (max Cs (max B 0 * Real.exp (Real.pi / 2))) 1 with hC'
  have hC'1 : 1 ≤ C' := le_max_right _ _
  have hC'0 : 0 < C' := by linarith
  have hpi := Real.pi_pos
  -- upper bound for `Γ(3/4 − iv/2)`
  have hup : ∀ v : ℝ, ‖Complex.Gamma (3 / 4 - ((v / 2 : ℝ) : ℂ) * I)‖ ≤
      C' * ((1 + |v|) ^ N * Real.exp (-(Real.pi * |v| / 4))) := by
    intro v
    have hv := abs_nonneg v
    have hpow1 : (1 : ℝ) ≤ (1 + |v|) ^ N := one_le_pow₀ (by linarith)
    rcases le_or_gt 2 |v| with h1 | h1
    · have him : (3 / 4 - ((v / 2 : ℝ) : ℂ) * I).im = -(v / 2) := by simp
      have hre : (3 / 4 - ((v / 2 : ℝ) : ℂ) * I).re = 3 / 4 := by simp
      have h := hs (3 / 4 - ((v / 2 : ℝ) : ℂ) * I) (by rw [hre]) (by rw [hre])
        (by rw [him, abs_neg, abs_div, abs_two]; linarith)
      rw [him, abs_neg, abs_div, abs_two] at h
      have hexp : Real.exp (-(Real.pi * (|v| / 2) / 2)) = Real.exp (-(Real.pi * |v| / 4)) := by
        congr 1; ring
      rw [hexp] at h
      have hpow : (|v| / 2) ^ N ≤ (1 + |v|) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith) N
      calc ‖Complex.Gamma (3 / 4 - ((v / 2 : ℝ) : ℂ) * I)‖
          ≤ Cs * (|v| / 2) ^ N * Real.exp (-(Real.pi * |v| / 4)) := h
        _ ≤ C' * (1 + |v|) ^ N * Real.exp (-(Real.pi * |v| / 4)) := by
            gcongr
            exact (le_max_left _ _).trans (le_max_left _ _)
        _ = _ := by ring
    · have hmem : v ∈ Set.Icc (-2 : ℝ) 2 := by
        rw [abs_lt] at h1; exact ⟨h1.1.le, h1.2.le⟩
      have hb := (hB v hmem).trans (le_max_left B 0)
      have hexp : Real.exp (-(Real.pi / 2)) ≤ Real.exp (-(Real.pi * |v| / 4)) := by
        apply Real.exp_le_exp.mpr; nlinarith
      have hB0 : 0 ≤ max B 0 := le_max_right _ _
      have hC'B : max B 0 * Real.exp (Real.pi / 2) ≤ C' :=
        (le_max_right _ _).trans (le_max_left _ _)
      calc ‖Complex.Gamma (3 / 4 - ((v / 2 : ℝ) : ℂ) * I)‖ ≤ max B 0 := hb
        _ = max B 0 * Real.exp (Real.pi / 2) * 1 * Real.exp (-(Real.pi / 2)) := by
            rw [mul_one, mul_assoc, ← Real.exp_add]; simp
        _ ≤ C' * (1 + |v|) ^ N * Real.exp (-(Real.pi * |v| / 4)) :=
            mul_le_mul (mul_le_mul hC'B hpow1 zero_le_one hC'0.le) hexp
              (by positivity) (by positivity)
        _ = _ := by ring
  refine ⟨Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi / C', by positivity, N, fun v => ?_⟩
  set ρ : ℂ := 1 / 2 + v * I with hρ
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (ρ / 2)
  have h1ρ : 1 - ρ / 2 = 3 / 4 - ((v / 2 : ℝ) : ℂ) * I := by rw [hρ]; push_cast; ring
  have hsin := norm_sin_le_exp_abs_im ((Real.pi : ℂ) * (ρ / 2))
  have him : ((Real.pi : ℂ) * (ρ / 2)).im = Real.pi * v / 2 := by rw [hρ]; simp; ring
  rw [him, abs_div, abs_mul, abs_of_pos hpi, abs_two] at hsin
  have hsinpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ := by
    rw [norm_pos_iff]
    intro h0
    have := hrefl
    rw [h0, div_zero] at this
    exact mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by rw [hρ]; simp))
      (Complex.Gamma_ne_zero_of_re_pos (by rw [hρ]; simp; norm_num)) this
  have hprod : ‖Complex.Gamma (ρ / 2)‖ * ‖Complex.Gamma (1 - ρ / 2)‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ := by
    rw [← norm_mul, hrefl, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have hlow : Real.pi * Real.exp (-(Real.pi * |v| / 2)) ≤
      ‖Complex.Gamma (ρ / 2)‖ * ‖Complex.Gamma (1 - ρ / 2)‖ := by
    rw [hprod, le_div_iff₀ hsinpos]
    calc Real.pi * Real.exp (-(Real.pi * |v| / 2)) * ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖
        ≤ Real.pi * Real.exp (-(Real.pi * |v| / 2)) * Real.exp (Real.pi * |v| / 2) := by
          gcongr
      _ = Real.pi := by rw [mul_assoc, ← Real.exp_add]; simp
  rw [h1ρ] at hlow
  have hU := hup v
  have hΓℝ : ‖Complex.Gammaℝ ρ‖ = Real.pi ^ (-(1 / 4 : ℝ)) * ‖Complex.Gamma (ρ / 2)‖ := by
    rw [Complex.Gammaℝ_def, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    congr 2
    rw [hρ]; simp; norm_num
  rw [hΓℝ]
  set X := (1 + |v|) ^ N with hX
  set e4 := Real.exp (-(Real.pi * |v| / 4)) with he4
  have he2 : Real.exp (-(Real.pi * |v| / 2)) = e4 * e4 := by
    rw [he4, ← Real.exp_add]; congr 1; ring
  rw [he2] at hlow
  have hX0 : 0 < X := by positivity
  have he40 : 0 < e4 := Real.exp_pos _
  have hG0 := norm_nonneg (Complex.Gamma (ρ / 2))
  have hpow0 : 0 < Real.pi ^ (-(1 / 4 : ℝ)) := by positivity
  -- `π e4² ≤ ‖Γ(ρ/2)‖ C' X e4`, hence `π e4 ≤ C' X ‖Γ(ρ/2)‖`
  have key : Real.pi * e4 ≤ C' * (X * ‖Complex.Gamma (ρ / 2)‖) := by
    have h := hlow.trans (mul_le_mul_of_nonneg_left hU hG0)
    have h' : Real.pi * e4 * e4 ≤ (C' * (X * ‖Complex.Gamma (ρ / 2)‖)) * e4 := by
      calc Real.pi * e4 * e4 = Real.pi * (e4 * e4) := by ring
        _ ≤ ‖Complex.Gamma (ρ / 2)‖ * (C' * (X * e4)) := h
        _ = (C' * (X * ‖Complex.Gamma (ρ / 2)‖)) * e4 := by ring
    exact le_of_mul_le_mul_right h' he40
  rw [div_mul_eq_mul_div, div_le_iff₀ hC'0]
  calc Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi * e4 = Real.pi ^ (-(1 / 4 : ℝ)) * (Real.pi * e4) := by
        ring
    _ ≤ Real.pi ^ (-(1 / 4 : ℝ)) * (C' * (X * ‖Complex.Gamma (ρ / 2)‖)) :=
        mul_le_mul_of_nonneg_left key hpow0.le
    _ = X * (Real.pi ^ (-(1 / 4 : ℝ)) * ‖Complex.Gamma (ρ / 2)‖) * C' := by ring

/-! ### The completed function -/

/-- The full Herglotz series: integer atoms plus real atoms. -/
def phiTot {J : ℕ} (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) (s : ℂ) : ℂ :=
  atomicPairSeries (fun j => Real.pi * m j) t s + ∑ k, fracTerm (c k) (u k) s

/-- `K = G(2)/(Q(2) R(2))`. -/
def kF {J : ℕ} (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) : ℂ :=
  bigG lam 2 / (atomQ m t 2 * fracProd c u 2)

/-- `Ĝ = K Q R`: holomorphic on `Re s > ½`, continuous on `Re s ≥ ½`. -/
def ghatF {J : ℕ} (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) (s : ℂ) : ℂ :=
  kF lam m t c u * (atomQ m t s * fracProd c u s)

section Completed

variable {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {J : ℕ} {c u : Fin J → ℝ}

theorem ne_atomAt_of_half_lt {z : ℂ} (hz : 1 / 2 < z.re) : ∀ i : AtomIndex m, z ≠ atomAt t i :=
  ne_atomAt_of_re_ne (ne_of_gt hz)

theorem hasDerivAt_QR (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hu : ∀ k, 0 < u k) {z : ℂ} (hz : 1 / 2 < z.re) :
    HasDerivAt (fun s => atomQ m t s * fracProd c u s)
      (phiTot m t c u z * (atomQ m t z * fracProd c u z)) z := by
  have hz1 : ∀ i : AtomIndex m, z ≠ atomAt t i := ne_atomAt_of_half_lt hz
  have hQd := (differentiable_atomQ hone hsum z).hasDerivAt
  have hL := logDeriv_atomQ hone hsum hz1
  rw [logDeriv_apply] at hL
  have hne := atomQ_ne_zero hone hsum hz1
  have e : deriv (atomQ m t) z = atomicPairSeries (fun j => Real.pi * m j) t z * atomQ m t z := by
    rw [← hL]; field_simp
  rw [e] at hQd
  have hR := hasDerivAt_fracProd (c := c) hu hz
  refine (hQd.mul hR).congr_deriv ?_
  unfold phiTot
  ring

theorem QR_ne_zero (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hu : ∀ k, 0 < u k) {z : ℂ} (hz : 1 / 2 < z.re) : atomQ m t z * fracProd c u z ≠ 0 :=
  mul_ne_zero (atomQ_ne_zero hone hsum (ne_atomAt_of_half_lt hz)) (fracProd_ne_zero hu hz)

/-- **`G = K Q R` on `Re s > 1`.** -/
theorem bigG_eq_ghatF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hu : ∀ k, 0 < u k)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = phiTot m t c u s)
    {s : ℂ} (hs : 1 < s.re) : bigG lam s = ghatF lam m t c u s := by
  set V : Set ℂ := {z : ℂ | 1 < z.re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hVc : Convex ℝ V := convex_halfSpace_re_gt 1
  set P : ℂ → ℂ := fun z => atomQ m t z * fracProd c u z with hP
  have hhalf : ∀ z ∈ V, 1 / 2 < z.re := fun z hz => by
    have : (1 : ℝ) < z.re := hz
    linarith
  have hPne : ∀ z ∈ V, P z ≠ 0 := fun z hz => QR_ne_zero hone hsum hu (hhalf z hz)
  have hPd : ∀ z ∈ V, HasDerivAt P (phiTot m t c u z * P z) z := fun z hz =>
    hasDerivAt_QR hone hsum hu (hhalf z hz)
  set r : ℂ → ℂ := fun z => bigG lam z / P z with hr
  have hrd : DifferentiableOn ℂ r V := fun z hz =>
    ((hasDerivAt_bigG hsl hz).differentiableAt.div (hPd z hz).differentiableAt
      (hPne z hz)).differentiableWithinAt
  have hderiv : Set.EqOn (deriv r) 0 V := by
    intro z hz
    have hG := hasDerivAt_bigG hsl (show 1 < z.re from hz)
    have hd : HasDerivAt r _ z := hG.div (hPd z hz) (hPne z hz)
    rw [hd.deriv, ← hid z hz]
    have hze : zetaArchimedeanDatum z = 1 / z + gammaRealLogConnection z := by
      unfold zetaArchimedeanDatum gammaRealLogConnection; ring
    rw [hze]
    simp only [Pi.zero_apply]
    ring
  have h2 : (2 : ℂ) ∈ V := by simp [hV]
  have hc := hVo.is_const_of_deriv_eq_zero hVc.isPreconnected hrd hderiv hs h2
  simp only [hr] at hc
  rw [div_eq_iff (hPne s hs)] at hc
  rw [hc]
  rfl

theorem hasDerivAt_ghatF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hu : ∀ k, 0 < u k) {z : ℂ} (hz : 1 / 2 < z.re) :
    HasDerivAt (ghatF lam m t c u) (phiTot m t c u z * ghatF lam m t c u z) z := by
  have h := (hasDerivAt_QR (c := c) hone hsum hu hz).const_mul (kF lam m t c u)
  refine h.congr_deriv ?_
  unfold ghatF
  ring

theorem differentiableOn_ghatF (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hu : ∀ k, 0 < u k) :
    DifferentiableOn ℂ (ghatF lam m t c u) {z : ℂ | 1 / 2 < z.re} := fun _ hz =>
  (hasDerivAt_ghatF hone hsum hu hz).differentiableAt.differentiableWithinAt

theorem continuousAt_ghatF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k) {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ContinuousAt (ghatF lam m t c u) z := by
  unfold ghatF
  exact continuousAt_const.mul ((differentiable_atomQ hone hsum).continuous.continuousAt.mul
    (continuousAt_fracProd hc hu hz))

/-- **Positivity of the total Herglotz series** on `Re z > ½`. -/
theorem re_phiTot_nonneg (hc : ∀ k, 0 ≤ c k) {z : ℂ} (hz : 1 / 2 < z.re) :
    0 ≤ (phiTot m t c u z).re := by
  unfold phiTot
  rw [Complex.add_re, Complex.re_sum]
  refine add_nonneg (re_atomicPairSeries_nonneg m t hz) (Finset.sum_nonneg fun k _ => ?_)
  unfold fracTerm
  rw [Complex.re_ofReal_mul]
  have hw : 0 < (z - 1 / 2).re := by simp; linarith
  exact mul_nonneg (hc k) (re_two_mul_div_nonneg hw (u k))

/-- **Horizontal monotonicity.**  `|Ĝ(σ + iτ)| ≤ |Ĝ(2 + iτ)|` for `½ ≤ σ ≤ 2`. -/
theorem norm_ghatF_le_two (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k) {σ : ℝ} (τ : ℝ) (h1 : 1 / 2 ≤ σ) (h2 : σ ≤ 2) :
    ‖ghatF lam m t c u (σ + τ * I)‖ ≤ ‖ghatF lam m t c u (2 + τ * I)‖ := by
  set φ : ℝ → ℝ := fun x => ‖ghatF lam m t c u (x + τ * I)‖ ^ 2 with hφ
  have hcont : ContinuousOn φ (Set.Icc (1 / 2) 2) := by
    intro x hx
    have hre : 1 / 2 ≤ ((x : ℂ) + τ * I).re := by simpa using hx.1
    have h := (continuousAt_ghatF (lam := lam) hone hsum hc hu hre).comp
      (f := fun y : ℝ => (y : ℂ) + τ * I) (by fun_prop)
    exact (h.norm.pow 2).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2, HasDerivAt φ
      (2 * inner ℝ (ghatF lam m t c u (x + τ * I))
        (phiTot m t c u (x + τ * I) * ghatF lam m t c u (x + τ * I))) x := by
    intro x hx
    have hre : 1 / 2 < ((x : ℂ) + τ * I).re := by simpa using hx.1
    have hd := hasDerivAt_ghatF (lam := lam) (c := c) hone hsum hu hre
    have hd2 : HasDerivAt (fun y : ℂ => ghatF lam m t c u (y + τ * I))
        (phiTot m t c u (x + τ * I) * ghatF lam m t c u (x + τ * I)) (x : ℂ) :=
      hd.comp_add_const _ _
    exact hd2.comp_ofReal.norm_sq
  have hnonneg : ∀ x ∈ Set.Ioo (1 / 2 : ℝ) 2, 0 ≤ 2 * inner ℝ (ghatF lam m t c u (x + τ * I))
      (phiTot m t c u (x + τ * I) * ghatF lam m t c u (x + τ * I)) := by
    intro x hx
    rw [Complex.inner]
    set g := ghatF lam m t c u (x + τ * I)
    set Φ := phiTot m t c u (x + τ * I)
    have e : Φ * g * (starRingEnd ℂ) g = ((Complex.normSq g : ℝ) : ℂ) * Φ := by
      rw [mul_assoc, Complex.mul_conj]; ring
    rw [e, Complex.re_ofReal_mul]
    have hre : 1 / 2 < ((x : ℂ) + τ * I).re := by simpa using hx.1
    exact mul_nonneg (by norm_num) (mul_nonneg (Complex.normSq_nonneg _)
      (re_phiTot_nonneg hc hre))
  have hmono : MonotoneOn φ (Set.Icc (1 / 2) 2) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hcont ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hderiv x hx).deriv]
      exact hnonneg x hx
  have h := hmono ⟨h1, h2⟩ ⟨by norm_num, le_rfl⟩ h2
  simp only [hφ] at h
  push_cast at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- **Growth of `G` on `Re s = 2`.** -/
theorem exists_bound_bigG_two
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ τ : ℝ,
      ‖bigG lam (2 + τ * I)‖ ≤ C * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
  obtain ⟨Cγ, Nγ, hCγ, hγ⟩ := exists_bound_Gammaℝ_two
  set S : ℝ := ∑' n, ‖LSeries.term (lamLog lam) 2 n‖ with hS
  refine ⟨Cγ * Real.exp S, Nγ + 2, by positivity, fun τ => ?_⟩
  have hre : (1 : ℝ) < (2 + (τ : ℂ) * I).re := by simp
  unfold bigG zetaOf
  have hsumm : LSeriesSummable (lamLog lam) (2 + τ * I) :=
    lseriesSummable_of_le (norm_lamLog_le lam) hsl hre
  have hL : ‖LSeries (lamLog lam) (2 + τ * I)‖ ≤ S := by
    unfold LSeries
    refine (norm_tsum_le_tsum_norm hsumm.norm).trans (le_of_eq (tsum_congr fun n => ?_))
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
    simp
  have hz : ‖Complex.exp (LSeries (lamLog lam) (2 + τ * I))‖ ≤ Real.exp S := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hL)
  have hτ := abs_nonneg τ
  have h1 : ‖(2 + (τ : ℂ) * I)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I)‖ ≤ ‖(2 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have h2 : ‖(2 + (τ : ℂ) * I - 1)‖ ≤ |τ| + 4 := by
    calc ‖(2 + (τ : ℂ) * I - 1)‖ = ‖(1 : ℂ) + (τ : ℂ) * I‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 1 + |τ| := by simp
      _ ≤ |τ| + 4 := by linarith
  have hE : 0 ≤ (|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)) := by positivity
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖(2 + (τ : ℂ) * I)‖ * ‖(2 + (τ : ℂ) * I - 1)‖ * ‖Complex.Gammaℝ (2 + τ * I)‖ *
        ‖Complex.exp (LSeries (lamLog lam) (2 + τ * I))‖
      ≤ (|τ| + 4) * (|τ| + 4) * (Cγ * ((|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)))) *
          Real.exp S := by
        gcongr
        exact hγ τ
    _ = Cγ * Real.exp S * ((|τ| + 4) ^ (Nγ + 2) * Real.exp (-(Real.pi * |τ| / 4))) := by ring

/-- **Growth of `Ĝ` on the strip `½ ≤ Re s ≤ 2`.** -/
theorem exists_bound_ghatF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = phiTot m t c u s) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 →
      ‖ghatF lam m t c u (σ + τ * I)‖ ≤ C * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
  obtain ⟨C, N, hC, h⟩ := exists_bound_bigG_two hsl
  refine ⟨C, N, hC, fun σ τ h1 h2 => ?_⟩
  have hre : (1 : ℝ) < (2 + (τ : ℂ) * I).re := by simp
  refine (norm_ghatF_le_two hone hsum hc hu τ h1 h2).trans ?_
  rw [← bigG_eq_ghatF hone hsum hu hsl hid hre]
  exact h τ

end Completed

/-! ### The removable singularity at `s = 1` and the decay -/

/-- `β = Ĝ(1)/2`. -/
def betaF {J : ℕ} (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) : ℂ :=
  ghatF lam m t c u 1 / 2

/-- `Ĝ − β · s(s−1)Γ_ℝ(s−1)`, which vanishes at `s = 1`. -/
def numNF {J : ℕ} (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) (s : ℂ) : ℂ :=
  ghatF lam m t c u s - betaF lam m t c u * mFactor s

/-- `E(s) = Ĝ(s)/(s(s−1)) − β Γ_ℝ(s−1)`, continued across `s = 1`. -/
def bigEF {J : ℕ} (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) (s : ℂ) : ℂ :=
  dslope (numNF lam m t c u) 1 s / s

section Removable

variable {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {J : ℕ} {c u : Fin J → ℝ}

theorem numNF_one : numNF lam m t c u 1 = 0 := by
  unfold numNF betaF; rw [mFactor_one]; ring

theorem bigEF_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    bigEF lam m t c u s =
      ghatF lam m t c u s / (s * (s - 1)) - betaF lam m t c u * Complex.Gammaℝ (s - 1) := by
  unfold bigEF
  rw [dslope_of_ne _ h1, slope_def_module, numNF_one, sub_zero, smul_eq_mul]
  unfold numNF
  rw [mFactor_eq h1]
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp

theorem differentiableOn_bigEF (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hu : ∀ k, 0 < u k) :
    DifferentiableOn ℂ (bigEF lam m t c u) {s : ℂ | 1 / 2 < s.re} := by
  have hopen : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hN : DifferentiableOn ℂ (numNF lam m t c u) {s : ℂ | 1 / 2 < s.re} := fun s hs => by
    have hs' : (1 / 2 : ℝ) < s.re := hs
    exact ((hasDerivAt_ghatF (lam := lam) (c := c) hone hsum hu hs').differentiableAt.sub
      ((differentiableAt_mFactor (by linarith)).const_mul _)).differentiableWithinAt
  have hD : DifferentiableOn ℂ (dslope (numNF lam m t c u) 1) {s : ℂ | 1 / 2 < s.re} :=
    (Complex.differentiableOn_dslope (hopen.mem_nhds (by norm_num))).mpr hN
  intro s hs
  have hs0 : s ≠ 0 := by
    intro h
    have hs' : (1 / 2 : ℝ) < s.re := hs
    rw [h] at hs'; simp at hs'; linarith
  exact ((hD s hs).differentiableAt (hopen.mem_nhds hs)).div differentiableAt_id hs0
    |>.differentiableWithinAt

theorem continuousAt_bigEF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ContinuousAt (bigEF lam m t c u) s := by
  rcases eq_or_lt_of_le hs with heq | hlt
  · have hs1 : s ≠ 1 := ne_one_of_re_eq_half heq.symm
    have hs0 : s ≠ 0 := ne_zero_of_re_eq_half heq.symm
    have hN : ContinuousAt (numNF lam m t c u) s :=
      (continuousAt_ghatF hone hsum hc hu hs).sub
        ((differentiableAt_mFactor (by rw [← heq]; norm_num)).continuousAt.const_mul _)
    have hf : ContinuousAt (fun z => (numNF lam m t c u z - numNF lam m t c u 1) / (z - 1) / z)
        s :=
      ((hN.sub continuousAt_const).div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hs1)).div continuousAt_id hs0
    refine hf.congr ?_
    filter_upwards [(isClosed_singleton (x := (1 : ℂ))).isOpen_compl.mem_nhds hs1] with z hz
    have hz1 : z ≠ 1 := hz
    unfold bigEF
    rw [dslope_of_ne _ hz1, slope_def_module, smul_eq_mul]
    ring
  · exact ((differentiableOn_bigEF hone hsum hu) s hlt).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hlt) |>.continuousAt

/-- **Decay of `E`** on the closed strip `½ ≤ Re s ≤ 3/2`. -/
theorem exists_decay_bigEF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = phiTot m t c u s) :
    ∃ C : ℝ, ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖bigEF lam m t c u s‖ ≤ C / (1 + s.im ^ 2) := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := exists_bound_ghatF hone hsum hc hu hsl hid
  obtain ⟨K₁, hK₁0, hK₁⟩ := exists_bound_pow_mul_exp_neg (N₁ + 2)
  obtain ⟨C₃, hC₃, h₃⟩ := exists_decay_Gammaℝ_sub_one
  have hK : IsCompact (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn (bigEF lam m t c u)
      (Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4) := fun z hz => by
    rw [Complex.mem_reProdIm] at hz
    exact (continuousAt_bigEF hone hsum hc hu hz.1.1).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  set β := betaF lam m t c u with hβ
  refine ⟨max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0), fun s hs => ?_⟩
  rw [mem_verticalStrip] at hs
  set τ := s.im with hτ
  have hpos : 0 < 1 + τ ^ 2 := by positivity
  rcases le_or_gt 4 |τ| with h4 | h4
  · have hn1 : 4 ≤ ‖s‖ := h4.trans (Complex.abs_im_le_norm s)
    have hn2 : 4 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    have h0 : s ≠ 0 := by intro h; rw [h, norm_zero] at hn1; norm_num at hn1
    have h1 : s ≠ 1 := by intro h; rw [h, sub_self, norm_zero] at hn2; norm_num at hn2
    rw [bigEF_eq h0 h1]
    have hs_eq : (s.re : ℂ) + τ * I = s := Complex.re_add_im s
    have hg : ‖ghatF lam m t c u s‖ ≤
        C₁ * ((|τ| + 4) ^ N₁ * Real.exp (-(Real.pi * |τ| / 4))) := by
      rw [← hs_eq]
      exact h₁ s.re τ hs.1 (by linarith [hs.2])
    have hdec := pow_mul_exp_neg_le_div hK₁ (abs_nonneg τ)
    rw [sq_abs] at hdec
    have hden : 1 ≤ ‖s * (s - 1)‖ := by
      rw [norm_mul]; nlinarith
    have hΓ := h₃ s hs.1 hs.2 h4
    calc ‖ghatF lam m t c u s / (s * (s - 1)) - β * Complex.Gammaℝ (s - 1)‖
        ≤ ‖ghatF lam m t c u s / (s * (s - 1))‖ + ‖β‖ * ‖Complex.Gammaℝ (s - 1)‖ := by
          rw [← norm_mul]; exact norm_sub_le _ _
      _ ≤ ‖ghatF lam m t c u s‖ + ‖β‖ * (C₃ / (1 + τ ^ 2)) := by
          gcongr
          rw [norm_div]
          exact div_le_self (norm_nonneg _) hden
      _ ≤ C₁ * (K₁ / (1 + τ ^ 2)) + ‖β‖ * (C₃ / (1 + τ ^ 2)) := by
          gcongr
          exact hg.trans (mul_le_mul_of_nonneg_left hdec hC₁)
      _ = (C₁ * K₁ + ‖β‖ * C₃) / (1 + τ ^ 2) := by ring
      _ ≤ max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0) / (1 + τ ^ 2) := by
          gcongr; exact le_max_left _ _
  · have hab := abs_lt.mp h4
    have hmem : s ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ×ℂ Set.Icc (-4 : ℝ) 4 := by
      rw [Complex.mem_reProdIm]
      exact ⟨⟨hs.1, hs.2⟩, ⟨hab.1.le, hab.2.le⟩⟩
    have hb := (hB s hmem).trans (le_max_left B 0)
    have hτ2 : τ ^ 2 ≤ 16 := by nlinarith
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    calc ‖bigEF lam m t c u s‖ ≤ max B 0 := hb
      _ ≤ 17 * max B 0 / (1 + τ ^ 2) := by
          rw [le_div_iff₀ hpos]; nlinarith
      _ ≤ max (C₁ * K₁ + ‖β‖ * C₃) (17 * max B 0) / (1 + τ ^ 2) := by
          gcongr; exact le_max_right _ _

end Removable

/-! ### Boundary values and the reflection defect on the critical line -/

/-- The point `½ + 2iτ` of the critical line. -/
def lineS (τ : ℝ) : ℂ := 2 * (((1 / 4 : ℝ) : ℂ) + τ * I)

theorem lineS_re (τ : ℝ) : (lineS τ).re = 1 / 2 := by unfold lineS; simp; norm_num

theorem lineS_eq (τ : ℝ) : lineS τ = 1 / 2 + ((2 * τ : ℝ) : ℂ) * I := by
  unfold lineS; push_cast; ring

theorem one_sub_lineS (τ : ℝ) : 1 - lineS τ = lineS (-τ) := by
  unfold lineS; push_cast; ring

theorem one_sub_lineS_eq_conj (τ : ℝ) : 1 - lineS τ = starRingEnd ℂ (lineS τ) := by
  apply Complex.ext <;> norm_num [lineS]

theorem lineS_ne_zero (τ : ℝ) : lineS τ ≠ 0 := ne_zero_of_re_eq_half (lineS_re τ)

theorem lineS_ne_one (τ : ℝ) : lineS τ ≠ 1 := ne_one_of_re_eq_half (lineS_re τ)

theorem Gammaℝ_lineS_ne_zero (τ : ℝ) : Complex.Gammaℝ (lineS τ) ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by rw [lineS_re]; norm_num)

theorem norm_lineS_mul_sub_one (τ : ℝ) : 1 / 4 ≤ ‖lineS τ * (lineS τ - 1)‖ := by
  have e : lineS τ * (lineS τ - 1) = ((-(1 / 4 + 4 * τ ^ 2) : ℝ) : ℂ) := by
    rw [lineS_eq]; push_cast; ring_nf; rw [I_sq]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  nlinarith [sq_nonneg τ]

/-- The boundary value `Φ(τ) = f(½ + 2iτ)`. -/
def phiF {J : ℕ} (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) (τ : ℝ) : ℂ :=
  ghatF lam m t c u (lineS τ) / (lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ))

/-- The reflection defect `g(τ) = (Λ(s) − Λ(1 − s))/Γ_ℝ(s)` at `s = ½ + 2iτ`. -/
def gF {J : ℕ} (lam : ℕ → ℝ) (m : ℕ → ℕ) (t : ℕ → ℝ) (c u : Fin J → ℝ) (τ : ℝ) : ℂ :=
  (ghatF lam m t c u (lineS τ) - ghatF lam m t c u (1 - lineS τ)) /
    (lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ))

section Line

variable {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {J : ℕ} {c u : Fin J → ℝ}

theorem bigEF_add_eq_phiF (τ : ℝ) :
    bigEF lam m t c u (lineS τ) + betaF lam m t c u * Complex.Gammaℝ (lineS τ - 1) =
      Complex.Gammaℝ (lineS τ) * phiF lam m t c u τ := by
  rw [bigEF_eq (lineS_ne_zero τ) (lineS_ne_one τ)]
  unfold phiF
  have h1 : lineS τ - 1 ≠ 0 := sub_ne_zero.mpr (lineS_ne_one τ)
  have h0 := lineS_ne_zero τ
  have hΓ := Gammaℝ_lineS_ne_zero τ
  field_simp
  ring

theorem bigEF_sub_eq_gF {s : ℂ} (hs : s.re = 1 / 2) :
    bigEF lam m t c u s - bigEF lam m t c u (1 - s) =
      -(betaF lam m t c u * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) +
        Complex.Gammaℝ s * gF lam m t c u (s.im / 2) := by
  have hsl : lineS (s.im / 2) = s := by
    apply Complex.ext
    · rw [lineS_re, hs]
    · simp [lineS]; ring
  have h0 : s ≠ 0 := ne_zero_of_re_eq_half hs
  have h1 : s ≠ 1 := ne_one_of_re_eq_half hs
  have hre' : (1 - s).re = 1 / 2 := by simp [hs]; norm_num
  have h0' : 1 - s ≠ 0 := ne_zero_of_re_eq_half hre'
  have h1' : 1 - s ≠ 1 := ne_one_of_re_eq_half hre'
  rw [bigEF_eq h0 h1, bigEF_eq h0' h1']
  unfold gF
  rw [hsl]
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hden : (1 - s) * (1 - s - 1) = s * (s - 1) := by ring
  rw [hden, show (1 : ℂ) - s - 1 = -s by ring]
  field_simp
  ring

theorem continuous_phiF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k) : Continuous (phiF lam m t c u) := by
  have hl : Continuous lineS := by unfold lineS; fun_prop
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  have hG : ContinuousAt (fun τ => ghatF lam m t c u (lineS τ)) τ :=
    (continuousAt_ghatF hone hsum hc hu (le_of_eq (lineS_re τ).symm)).comp hl.continuousAt
  have hΓ : ContinuousAt (fun τ => Complex.Gammaℝ (lineS τ)) τ :=
    ((differentiableAt_Gammaℝ (by rw [lineS_re]; norm_num)).continuousAt).comp hl.continuousAt
  have hden : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
      (Gammaℝ_lineS_ne_zero τ)
  exact hG.div ((hl.continuousAt.mul (hl.continuousAt.sub continuousAt_const)).mul hΓ) hden

theorem continuous_gF (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k) : Continuous (gF lam m t c u) := by
  have hl : Continuous lineS := by unfold lineS; fun_prop
  refine continuous_iff_continuousAt.mpr fun τ => ?_
  have hG : ContinuousAt (fun τ => ghatF lam m t c u (lineS τ)) τ :=
    (continuousAt_ghatF hone hsum hc hu (le_of_eq (lineS_re τ).symm)).comp hl.continuousAt
  have hG' : ContinuousAt (fun τ => ghatF lam m t c u (1 - lineS τ)) τ := by
    have hre : 1 / 2 ≤ (1 - lineS τ).re := by rw [one_sub_lineS, lineS_re]
    exact (continuousAt_ghatF hone hsum hc hu hre).comp (f := fun τ => 1 - lineS τ)
      ((continuous_const.sub hl).continuousAt)
  have hΓ : ContinuousAt (fun τ => Complex.Gammaℝ (lineS τ)) τ :=
    ((differentiableAt_Gammaℝ (by rw [lineS_re]; norm_num)).continuousAt).comp hl.continuousAt
  have hden : lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
      (Gammaℝ_lineS_ne_zero τ)
  exact (hG.sub hG').div ((hl.continuousAt.mul (hl.continuousAt.sub continuousAt_const)).mul hΓ)
    hden

/-- **Polynomial bounds** for the boundary value and the defect. -/
theorem exists_poly_bound_line (hone : ∀ j, 1 ≤ t j)
    (hsum : Summable fun j => (m j : ℝ) / t j ^ 2) (hc : ∀ k, 0 ≤ c k) (hu : ∀ k, 0 < u k)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = phiTot m t c u s) :
    ∃ CB : ℝ, ∃ N : ℕ, 0 ≤ CB ∧ ∀ τ : ℝ, ‖phiF lam m t c u τ‖ ≤ CB * (1 + |τ|) ^ N ∧
      ‖gF lam m t c u τ‖ ≤ CB * (1 + |τ|) ^ N := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := exists_bound_ghatF hone hsum hc hu hsl hid
  obtain ⟨cl, hcl, M, hlow⟩ := exists_lower_bound_Gammaℝ_half_line
  refine ⟨2 * (4 * C₁ / cl) * 4 ^ N₁ * 2 ^ M, N₁ + M, by positivity, fun τ => ?_⟩
  have hτ := abs_nonneg τ
  set v : ℝ := 2 * τ with hv
  have hav : |v| = 2 * |τ| := by rw [hv, abs_mul, abs_two]
  set e4 := Real.exp (-(Real.pi * |v| / 4)) with he4
  have he40 : 0 < e4 := Real.exp_pos _
  -- bounds on `Ĝ` at `½ ± 2iτ`
  have hg1 : ‖ghatF lam m t c u (lineS τ)‖ ≤ C₁ * ((|v| + 4) ^ N₁ * e4) := by
    rw [lineS_eq, ← hv, he4]
    have h := h₁ (1 / 2) v le_rfl (by norm_num)
    have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    rwa [e] at h
  have hg2 : ‖ghatF lam m t c u (1 - lineS τ)‖ ≤ C₁ * ((|v| + 4) ^ N₁ * e4) := by
    rw [one_sub_lineS, lineS_eq, he4]
    have h := h₁ (1 / 2) (2 * -τ) le_rfl (by norm_num)
    have habs : |2 * -τ| = |v| := by rw [hv, mul_neg, abs_neg]
    rw [habs] at h
    have e : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    rwa [e] at h
  -- lower bound on the denominator
  have hΓl := hlow v
  rw [← lineS_eq] at hΓl
  have hden : cl * e4 / ((1 + |v|) ^ M) * (1 / 4) ≤
      ‖lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)‖ := by
    rw [norm_mul]
    have h1 := norm_lineS_mul_sub_one τ
    have h2 : cl * e4 / ((1 + |v|) ^ M) ≤ ‖Complex.Gammaℝ (lineS τ)‖ := by
      rw [div_le_iff₀ (by positivity)]; linarith
    calc cl * e4 / ((1 + |v|) ^ M) * (1 / 4) = (1 / 4) * (cl * e4 / ((1 + |v|) ^ M)) := by ring
      _ ≤ ‖lineS τ * (lineS τ - 1)‖ * ‖Complex.Gammaℝ (lineS τ)‖ :=
          mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
  have hdenpos : 0 < cl * e4 / ((1 + |v|) ^ M) * (1 / 4) := by positivity
  -- the polynomial factors
  have hp1 : (|v| + 4) ^ N₁ ≤ 4 ^ N₁ * (1 + |τ|) ^ N₁ := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by rw [hav]; linarith) _
  have hp2 : (1 + |v|) ^ M ≤ 2 ^ M * (1 + |τ|) ^ M := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by rw [hav]; linarith) _
  -- a common bound for numerators `‖X‖ ≤ 2 C₁ (|v|+4)^N₁ e4`
  have key : ∀ X : ℂ, ‖X‖ ≤ 2 * (C₁ * ((|v| + 4) ^ N₁ * e4)) →
      ‖X / (lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ))‖ ≤
        2 * (4 * C₁ / cl) * 4 ^ N₁ * 2 ^ M * (1 + |τ|) ^ (N₁ + M) := by
    intro X hX
    rw [norm_div, div_le_iff₀ (lt_of_lt_of_le hdenpos hden)]
    refine hX.trans ?_
    calc 2 * (C₁ * ((|v| + 4) ^ N₁ * e4))
        = 2 * (4 * C₁ / cl) * (|v| + 4) ^ N₁ * (1 + |v|) ^ M *
            (cl * e4 / ((1 + |v|) ^ M) * (1 / 4)) := by
          field_simp
      _ ≤ 2 * (4 * C₁ / cl) * (4 ^ N₁ * (1 + |τ|) ^ N₁) * (2 ^ M * (1 + |τ|) ^ M) *
            ‖lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)‖ := by
          gcongr
      _ = 2 * (4 * C₁ / cl) * 4 ^ N₁ * 2 ^ M * (1 + |τ|) ^ (N₁ + M) *
            ‖lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)‖ := by
          rw [pow_add]; ring
  refine ⟨key _ ?_, key _ ?_⟩
  · have := norm_nonneg (ghatF lam m t c u (lineS τ))
    nlinarith [mul_nonneg hC₁ (mul_nonneg (pow_nonneg (by positivity : (0:ℝ) ≤ |v| + 4) N₁)
      he40.le)]
  · exact (norm_sub_le _ _).trans (by linarith)

/-- **The twisted reflection law above the real atoms.** -/
theorem gF_eq_of_gt (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hu : ∀ k, 0 < u k) {τ : ℝ} (hτ : ∑ k, u k < τ) :
    gF lam m t c u τ =
      (1 - Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I)) * phiF lam m t c u τ := by
  have hy : ∀ k, u k < 2 * τ := fun k => by
    have h1 : u k ≤ ∑ j, u j :=
      Finset.single_le_sum (fun j _ => (hu j).le) (Finset.mem_univ k)
    have h2 : 0 ≤ ∑ j, u j := Finset.sum_nonneg fun j _ => (hu j).le
    linarith
  have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
  have hrefl : ghatF lam m t c u (1 - lineS τ) =
      Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I) * ghatF lam m t c u (lineS τ) := by
    unfold ghatF
    rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracProd_conj hu hre, lineS_eq,
      conj_fracProd_of_gt hu hy]
    ring
  unfold gF phiF
  rw [hrefl]
  ring

/-- **The twisted reflection law below the real atoms.** -/
theorem gF_eq_of_lt (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hu : ∀ k, 0 < u k) {τ : ℝ} (hτ : τ < -∑ k, u k) :
    gF lam m t c u τ =
      (1 - (Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I))⁻¹) * phiF lam m t c u τ := by
  have hy : ∀ k, u k < -(2 * τ) := fun k => by
    have h1 : u k ≤ ∑ j, u j :=
      Finset.single_le_sum (fun j _ => (hu j).le) (Finset.mem_univ k)
    have h2 : 0 ≤ ∑ j, u j := Finset.sum_nonneg fun j _ => (hu j).le
    linarith
  have hre : (1 / 2 : ℝ) ≤ (lineS τ).re := le_of_eq (lineS_re τ).symm
  have hline : lineS τ = 1 / 2 - ((-(2 * τ) : ℝ) : ℂ) * I := by
    rw [lineS_eq]; push_cast; ring
  have hrefl : ghatF lam m t c u (1 - lineS τ) =
      (Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I))⁻¹ *
        ghatF lam m t c u (lineS τ) := by
    unfold ghatF
    rw [atomQ_one_sub hone hsum, one_sub_lineS_eq_conj, fracProd_conj hu hre, hline,
      conj_fracProd_of_lt hu hy]
    ring
  unfold gF phiF
  rw [hrefl]
  ring

end Line

/-! ### Finitely many real masses force `Λ` and RH -/

/-- **Finitely many non-integer spectral masses force `Λ` and the Riemann hypothesis.**  Let
`Σ_n |lam(n)| n^{-σ} < ∞` for `σ > 1`.  Suppose that on `Re s > 1`
`Γ̃(s) + 1/(s−1) − Σ_{n≥2} lam(n) n^{-s}` equals the Herglotz series with integer masses `m_j` at
ordinates `t_j ≥ 1` (`Σ m_j/t_j² < ∞`) plus finitely many real masses `c_k ≥ 0` at ordinates
`u_k ≥ 1`.  Then `lam(n) = Λ(n)` for every `n ≥ 2`, and the Riemann hypothesis holds. -/
theorem fractional_mass_rigidity {lam : ℕ → ℝ} {m : ℕ → ℕ} {t : ℕ → ℝ} {J : ℕ}
    {c u : Fin J → ℝ} (hone : ∀ j, 1 ≤ t j) (hsum : Summable fun j => (m j : ℝ) / t j ^ 2)
    (hc : ∀ k, 0 ≤ c k) (hu1 : ∀ k, 1 ≤ u k)
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hid : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (fun n => if 2 ≤ n then (lam n : ℂ) else 0) s =
        atomicPairSeries (fun j => Real.pi * m j) t s +
          ∑ k, (c k : ℂ) * (2 * (s - 1 / 2) / ((s - 1 / 2) ^ 2 + (u k : ℂ) ^ 2))) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hu : ∀ k, 0 < u k := fun k => lt_of_lt_of_le one_pos (hu1 k)
  have hid' : ∀ s : ℂ, 1 < s.re → zetaArchimedeanDatum s + 1 / (s - 1) -
      LSeries (lamTwo lam) s = phiTot m t c u s := hid
  set a := dirichletExp (lamLog lam) with ha_def
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ :=
    fun σ hσ => summable_coeff_of_LSeriesSummable (hLa σ (by simpa using hσ)).1
  obtain ⟨C, hC⟩ := exists_decay_bigEF hone hsum hc hu hsl hid'
  obtain ⟨CB, N, hCB, hB⟩ := exists_poly_bound_line hone hsum hc hu hsl hid'
  have hdE := differentiableOn_bigEF (lam := lam) (c := c) hone hsum hu
  set β := betaF lam m t c u with hβ
  set κ : ℂ := Complex.exp (-((2 * Real.pi * ∑ k, c k : ℝ) : ℂ) * I) with hκ
  have hκ0 : κ ≠ 0 := Complex.exp_ne_zero _
  have hY : 0 ≤ ∑ k, u k := Finset.sum_nonneg fun k _ => (hu k).le
  have hzeroA : Tendsto (fun δ : ℝ => δ * HamburgerStability.abelMass (fun _ : ℝ => (0 : ℂ)) δ)
      (𝓝[>] 0) (𝓝 0) := by
    have : (fun δ : ℝ => δ * HamburgerStability.abelMass (fun _ : ℝ => (0 : ℂ)) δ) =
        fun _ => 0 := by
      funext δ; simp [HamburgerStability.abelMass]
    rw [this]; exact tendsto_const_nhds
  have hcoef := HamburgerTwisted.coeff_eq_of_critical_line_twisted_defect
    (a := a) ha (E := bigEF lam m t c u) (β := β) (C := C) (g := gF lam m t c u)
    (Φ := phiF lam m t c u) (r' := fun _ => 0) (CB := CB) (N := N)
    (fun z hz => by
      rw [mem_verticalStrip] at hz
      exact (continuousAt_bigEF hone hsum hc hu hz.1).continuousWithinAt)
    (hdE.mono fun z hz => by show (1 / 2 : ℝ) < z.re; exact hz.1)
    hC
    (fun s hs => by
      have h1 : 1 < s.re := by rw [hs]; norm_num
      have h0 : s ≠ 0 := by intro h; rw [h] at h1; simp at h1; linarith
      have hs1 : s ≠ 1 := by intro h; rw [h] at h1; simp at h1
      have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      rw [coeffDirichlet_eq_LSeries, (hLa s h1).2, bigEF_eq h0 hs1,
        ← bigG_eq_ghatF hone hsum hu hsl hid' h1]
      unfold bigG
      field_simp
      ring)
    (fun s hs => bigEF_sub_eq_gF hs)
    (fun τ => bigEF_add_eq_phiF τ)
    (continuous_gF hone hsum hc hu).measurable (fun τ => (hB τ).2)
    (continuous_phiF hone hsum hc hu).measurable (fun τ => (hB τ).1)
    measurable_const (fun τ => by simp; positivity)
    hzeroA hY hκ0
    (fun τ hτ => by rw [gF_eq_of_lt hone hsum hu hτ]; ring)
  -- all coefficients equal `a 1 = 1`
  have ha1 : a 1 = 1 := dirichletExp_one (lamLog_zero lam) (lamLog_one lam)
  have h2β : 2 * κ * β = 1 := by rw [← hcoef 0, ha1]
  have hall : ∀ {n : ℕ}, n ≠ 0 → a n = (1 : ℕ → ℂ) n := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hcoef k, h2β]; rfl
  have hζ : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s := by
    intro s hs
    rw [← (hLa s hs).2, LSeries_congr hall s, LSeries_one_eq_riemannZeta hs]
  -- `lam = Λ` on `n ≥ 2`
  have hLam : ∀ s : ℂ, 1 < s.re →
      LSeries (lamTwo lam) s = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
    intro s hs
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : riemannZeta =ᶠ[𝓝 s] zetaOf lam := by
      filter_upwards [hopen.mem_nhds hs] with z hz
      exact (hζ z hz).symm
    have hd := (hasDerivAt_zetaOf hsl hs).congr_of_eventuallyEq hev
    have hζne : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
    rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, hd.deriv, hζ s hs]
    field_simp
  have habs1 : LSeries.abscissaOfAbsConv (lamTwo lam) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => lseriesSummable_of_le (norm_lamTwo_le lam) hsl (by simpa using hy))
      (EReal.coe_lt_top 1)
  have habs2 :
      LSeries.abscissaOfAbsConv (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) < ⊤ :=
    lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
      fun y hy => ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hy))
      (EReal.coe_lt_top 1)
  have hEv : (fun x : ℝ => LSeries (lamTwo lam) x) =ᶠ[atTop]
      fun x : ℝ => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hLam x (by simpa using hx)
  refine ⟨fun n hn => ?_, ?_⟩
  · have h := LSeries.eq_of_LSeries_eventually_eq habs1 habs2 hEv (n := n) (by omega)
    simp only [lamTwo, if_pos hn] at h
    exact_mod_cast h
  -- the Riemann hypothesis
  · by_contra hRH
    obtain ⟨ρ, hρ0, hρ1, hρ2⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
    set Z : ℂ → ℂ := fun s => s * (s - 1) * completedRiemannZeta₀ s + 1 with hZ
    have hZd : Differentiable ℂ Z := by
      have := differentiable_completedZeta₀
      intro s; simp only [hZ]; fun_prop
    set U : Set ℂ := {z : ℂ | 1 / 2 < z.re} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    have hZa : AnalyticOnNhd ℂ Z U := hZd.differentiableOn.analyticOnNhd hUo
    have hGa : AnalyticOnNhd ℂ (ghatF lam m t c u) U :=
      (differentiableOn_ghatF (lam := lam) (c := c) hone hsum hu).analyticOnNhd hUo
    have hZΛ : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → Z s = s * (s - 1) * completedRiemannZeta s := by
      intro s h0 h1
      have h1' : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
      have h1'' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
      simp only [hZ]
      rw [completedRiemannZeta_eq]
      field_simp
      ring
    have hΛζ : ∀ s : ℂ, 0 < s.re → completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
      intro s hs
      have h0 : s ≠ 0 := by intro h; rw [h] at hs; simp at hs
      rw [riemannZeta_def_of_ne_zero h0]
      field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hs]
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : ghatF lam m t c u =ᶠ[𝓝 (2 : ℂ)] Z := by
      filter_upwards [hopen.mem_nhds (by norm_num : (1 : ℝ) < (2 : ℂ).re)] with z hz
      have hz' : 1 < z.re := hz
      have h0 : z ≠ 0 := by intro h; rw [h] at hz'; simp at hz'; linarith
      have h1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
      rw [hZΛ z h0 h1, hΛζ z (by linarith), ← hζ z hz',
        ← bigG_eq_ghatF hone hsum hu hsl hid' hz']
      unfold bigG; ring
    have h2U : (2 : ℂ) ∈ U := by simp [hU]; norm_num
    have hρU : ρ ∈ U := hρ1
    have hglob := hGa.eqOn_of_preconnected_of_eventuallyEq hZa
      (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected h2U hev hρU
    have hρne0 : ρ ≠ 0 := by intro h; rw [h] at hρ1; simp at hρ1; linarith
    have hρne1 : ρ ≠ 1 := by intro h; rw [h] at hρ2; simp at hρ2
    have hzero : ghatF lam m t c u ρ = 0 := by
      rw [hglob, hZΛ ρ hρne0 hρne1, hΛζ ρ (by linarith), hρ0, mul_zero, mul_zero]
    have hK : kF lam m t c u ≠ 0 := by
      unfold kF
      exact div_ne_zero (bigG_ne_zero lam (by norm_num)) (QR_ne_zero hone hsum hu (by norm_num))
    exact mul_ne_zero hK (QR_ne_zero hone hsum hu hρ1) hzero

end

end FractionalMassRigidity

end RHTower
