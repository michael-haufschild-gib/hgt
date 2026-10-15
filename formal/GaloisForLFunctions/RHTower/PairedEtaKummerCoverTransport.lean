import GaloisForLFunctions.RHTower.PairedEtaRootContinuationBoundary

/-!
# Explicit Kummer cover transport for the paired eta source

On `Re s < 1`, the exponential dilation correction has an explicit holomorphic
logarithm. Its coherent dyadic roots identify the Kummer covers of the genuine
zeta pole unit and the normalized paired eta source over the open half-strip.
The maps extend across every zero of the genuine source; no zero-free
hypothesis on that source enters their construction.
-/

noncomputable section

namespace RHTower.PairedEtaKummer

/-- The open right half of the critical strip. -/
abbrev HalfStrip := {s : ℂ // (1 / 2 : ℝ) < s.re ∧ s.re < 1}

/-- The actual cyclic root surface, including its branch points. -/
abbrev Cover (f : ℂ → ℂ) (d : ℕ) :=
  {p : HalfStrip × ℂ // p.2 ^ d = f p.1.val}

private def argument (h : ℝ) (s : ℂ) : ℂ := (h : ℂ) * (1 - s)

private theorem argument_re_pos {h : ℝ} (hh : 0 < h) {s : ℂ}
    (hs : s.re < 1) : 0 < (argument h s).re := by
  simp only [argument, Complex.mul_re, Complex.ofReal_re, Complex.sub_re,
    Complex.one_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos hh (sub_pos.mpr hs)

private theorem argument_slit {h : ℝ} (hh : 0 < h) {s : ℂ}
    (hs : s.re < 1) : argument h s ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (argument_re_pos hh hs))

private theorem correction_slit {h : ℝ} (hh : 0 < h) {s : ℂ}
    (hs : s.re < 1) : 1 - Complex.exp (-argument h s) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have he : ‖Complex.exp (-argument h s)‖ < 1 := by
    rw [Complex.norm_exp, Real.exp_lt_one_iff, Complex.neg_re]
    exact neg_neg_of_pos (argument_re_pos hh hs)
  have hr := Complex.re_le_norm (Complex.exp (-argument h s))
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- A logarithm of the dilation correction on the left half-plane `Re s < 1`. -/
def dilationLog (h : ℝ) (s : ℂ) : ℂ :=
  argument h s + Complex.log (1 - Complex.exp (-argument h s)) -
    Complex.log (argument h s)

theorem analyticAt_dilationLog {h : ℝ} (hh : 0 < h) {s : ℂ}
    (hs : s.re < 1) : AnalyticAt ℂ (dilationLog h) s := by
  have ha : AnalyticAt ℂ (argument h) s := by unfold argument; fun_prop
  have hb : AnalyticAt ℂ (fun s => 1 - Complex.exp (-argument h s)) s := by
    unfold argument
    fun_prop
  exact (ha.add (hb.clog (correction_slit hh hs))).sub
    (ha.clog (argument_slit hh hs))

theorem exp_dilationLog {h : ℝ} (hh : 0 < h) {s : ℂ}
    (hs : s.re < 1) : Complex.exp (dilationLog h s) = poleDilationCorrection h s := by
  have hz := Complex.slitPlane_ne_zero (argument_slit hh hs)
  have hb := Complex.slitPlane_ne_zero (correction_slit hh hs)
  have he := Complex.exp_ne_zero (argument h s)
  have harg : -(h : ℂ) * (s - 1) = argument h s := by unfold argument; ring
  have hj := poleDilationCorrection_exact h s
  rw [harg] at hj
  have hj' : argument h s * poleDilationCorrection h s =
      Complex.exp (argument h s) - 1 := by
    unfold argument at *
    linear_combination -hj
  rw [dilationLog, Complex.exp_sub, Complex.exp_add, Complex.exp_log hz,
    Complex.exp_log hb, Complex.exp_neg]
  field_simp
  linear_combination -hj'

/-- Explicit coherent dyadic roots of the dilation correction. -/
def dilationRoot (h : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (dilationLog h s / (2 : ℂ) ^ k)

theorem dilationRoot_ne_zero (h : ℝ) (k : ℕ) (s : ℂ) :
    dilationRoot h k s ≠ 0 := Complex.exp_ne_zero _

theorem analyticAt_dilationRoot {h : ℝ} (hh : 0 < h) (k : ℕ) {s : ℂ}
    (hs : s.re < 1) : AnalyticAt ℂ (dilationRoot h k) s := by
  exact (analyticAt_dilationLog hh hs).div_const.cexp

theorem dilationRoot_pow {h : ℝ} (hh : 0 < h) (k : ℕ) {s : ℂ}
    (hs : s.re < 1) : dilationRoot h k s ^ (2 ^ k) = poleDilationCorrection h s := by
  rw [dilationRoot, ← Complex.exp_nat_mul]
  have hd : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  have hc : ((2 ^ k : ℕ) : ℂ) = (2 : ℂ) ^ k := by norm_cast
  rw [hc]
  have hm : (2 : ℂ) ^ k * (dilationLog h s / (2 : ℂ) ^ k) = dilationLog h s := by
    field_simp
  rw [hm, exp_dilationLog hh hs]

theorem dilationRoot_succ_sq (h : ℝ) (k : ℕ) (s : ℂ) :
    dilationRoot h (k + 1) s ^ 2 = dilationRoot h k s := by
  unfold dilationRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hd : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num)
  rw [pow_succ]
  push_cast
  field_simp

theorem continuous_dilationRoot_halfStrip {h : ℝ} (hh : 0 < h) (k : ℕ) :
    Continuous (fun s : HalfStrip => dilationRoot h k s.val) := by
  have ha : AnalyticOnNhd ℂ (dilationRoot h k) {s : ℂ | s.re < 1} :=
    fun _ hs => analyticAt_dilationRoot hh k hs
  exact ha.continuousOn.comp_continuous continuous_subtype_val (fun s => s.property.2)

/-- Multiplication by a continuous root unit identifies the full cyclic surfaces. -/
def coverMulHomeomorph (f g : ℂ → ℂ) (d : ℕ) (r : HalfStrip → ℂ)
    (hc : Continuous r) (hn : ∀ s, r s ≠ 0)
    (hp : ∀ s : HalfStrip, r s ^ d * f s.val = g s.val) :
    Cover f d ≃ₜ Cover g d where
  toFun p := ⟨(p.val.1, r p.val.1 * p.val.2), by
    rw [mul_pow, p.property]; exact hp p.val.1⟩
  invFun p := ⟨(p.val.1, p.val.2 / r p.val.1), by
    rw [div_pow, p.property, ← hp p.val.1]
    exact mul_div_cancel_left₀ _ (pow_ne_zero d (hn p.val.1))⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact mul_div_cancel_left₀ _ (hn p.val.1)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      rw [mul_comm, div_mul_cancel₀ _ (hn p.val.1)]
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.fst.prodMk
      ((hc.comp continuous_subtype_val.fst).mul continuous_subtype_val.snd)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.fst.prodMk
      (continuous_subtype_val.snd.div (hc.comp continuous_subtype_val.fst)
        (fun p => hn p.val.1))

/-- Explicit cover transport from the pole unit to its positive dilation source. -/
def dilationCoverHomeomorph (h : ℝ) (hh : 0 < h) (k : ℕ) :
    Cover zetaPoleUnit (2 ^ k) ≃ₜ Cover (poleDilationSource h) (2 ^ k) :=
  coverMulHomeomorph zetaPoleUnit (poleDilationSource h) (2 ^ k)
    (fun s => dilationRoot h k s.val)
    (continuous_dilationRoot_halfStrip hh k) (fun s => dilationRoot_ne_zero h k s.val)
    (fun s => by rw [dilationRoot_pow hh k s.property.2]; rfl)

/-- Unconditional transport to the normalized paired eta source over the open half-strip. -/
def pairedEtaCoverHomeomorph (k : ℕ) :
    Cover zetaPoleUnit (2 ^ k) ≃ₜ Cover (fun s => etaPair s / (Real.log 2 : ℂ)) (2 ^ k) :=
  coverMulHomeomorph zetaPoleUnit (fun s => etaPair s / (Real.log 2 : ℂ)) (2 ^ k)
    (fun s => dilationRoot (Real.log 2) k s.val)
    (continuous_dilationRoot_halfStrip (Real.log_pos (by norm_num)) k)
    (fun s => dilationRoot_ne_zero _ k s.val)
    (fun s => by
      rw [dilationRoot_pow (Real.log_pos (by norm_num)) k s.property.2]
      exact poleDilationSource_log_two (by linarith [s.property.1]))

theorem pairedEtaCoverHomeomorph_base (k : ℕ) (p : Cover zetaPoleUnit (2 ^ k)) :
    (pairedEtaCoverHomeomorph k p).val.1 = p.val.1 := rfl

theorem pairedEtaCoverHomeomorph_fiber (k : ℕ) (p : Cover zetaPoleUnit (2 ^ k)) :
    (pairedEtaCoverHomeomorph k p).val.2 =
      dilationRoot (Real.log 2) k p.val.1.val * p.val.2 := rfl

/-- The dyadic transition map on the full root surface. -/
def squareLevel (f : ℂ → ℂ) (k : ℕ) (p : Cover f (2 ^ (k + 1))) :
    Cover f (2 ^ k) :=
  ⟨(p.val.1, p.val.2 ^ 2), by
    rw [← pow_mul]
    have hd : 2 * 2 ^ k = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
    rw [hd]
    exact p.property⟩

theorem continuous_squareLevel (f : ℂ → ℂ) (k : ℕ) : Continuous (squareLevel f k) := by
  unfold squareLevel
  fun_prop

/-- The explicit paired eta transport respects every dyadic transition. -/
theorem pairedEtaCoverHomeomorph_squareLevel (k : ℕ)
    (p : Cover zetaPoleUnit (2 ^ (k + 1))) :
    pairedEtaCoverHomeomorph k (squareLevel zetaPoleUnit k p) =
      squareLevel (fun s => etaPair s / (Real.log 2 : ℂ)) k
        (pairedEtaCoverHomeomorph (k + 1) p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change dilationRoot (Real.log 2) k p.val.1.val * p.val.2 ^ 2 =
      (dilationRoot (Real.log 2) (k + 1) p.val.1.val * p.val.2) ^ 2
    rw [mul_pow, dilationRoot_succ_sq]

/-- Multiplication by a root of unity on a cyclic root surface. -/
def deckMul (f : ℂ → ℂ) (d : ℕ) (ω : ℂ) (hω : ω ^ d = 1)
    (p : Cover f d) : Cover f d :=
  ⟨(p.val.1, ω * p.val.2), by rw [mul_pow, hω, one_mul]; exact p.property⟩

theorem continuous_deckMul (f : ℂ → ℂ) (d : ℕ) (ω : ℂ) (hω : ω ^ d = 1) :
    Continuous (deckMul f d ω hω) := by
  unfold deckMul
  fun_prop

/-- The paired eta identification commutes with every deck rotation. -/
theorem pairedEtaCoverHomeomorph_deckMul (k : ℕ) (ω : ℂ) (hω : ω ^ (2 ^ k) = 1)
    (p : Cover zetaPoleUnit (2 ^ k)) :
    pairedEtaCoverHomeomorph k (deckMul zetaPoleUnit (2 ^ k) ω hω p) =
      deckMul (fun s => etaPair s / (Real.log 2 : ℂ)) (2 ^ k) ω hω
        (pairedEtaCoverHomeomorph k p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change dilationRoot (Real.log 2) k p.val.1.val * (ω * p.val.2) =
      ω * (dilationRoot (Real.log 2) k p.val.1.val * p.val.2)
    ring

end RHTower.PairedEtaKummer
