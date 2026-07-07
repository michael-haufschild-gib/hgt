/-
The integer winding number of a nonvanishing loop, built from the `exp` covering map.

For a continuous nowhere-zero loop `γ : ℝ → ℂ` (`γ a = γ b`), the exponential covering map
`ℂ → ℂ∖{0}` lifts `γ` to a continuous logarithm `L` (`exp ∘ L = γ`) on the simply connected line
`ℝ`; the increment `L b − L a` lies in `2πiℤ` (the two endpoints have equal image) and is
independent of the branch `L` (two logs differ by a locally constant `2πiℤ`-valued function, hence a
constant on connected `ℝ`).  The winding number is the integer `k` with `L b − L a = 2πi·k`.

This is the loop realisation of the deck-charge obstruction: `w_k(γ) = windingNumber γ mod 2^k`
(`loopCharge`), the obstruction to a continuous `2^k`-th root along `γ`, and it is
additive (`windingNumber_mul`), scales under powers (`windingNumber_pow`), and vanishes exactly when
the logarithm closes up (`windingNumber_eq_zero_iff`).  mathlib supplies the branch of logarithm
(`Complex.exists_continuousOn_eqOn_exp_comp`) but not the integer winding number; it is built here.
-/
import GaloisForLFunctions.RHTower.DeckChargeCalculus

open Complex Set
open scoped Classical

namespace RHTower

/-! ### §1 Continuous logarithm on the line and branch-independence of the increment -/

/-- The real line (as `univ`) is simply connected: it is contractible. -/
theorem realUniv_isSimplyConnected : IsSimplyConnected (Set.univ : Set ℝ) := by
  haveI : ContractibleSpace ↥(Set.univ : Set ℝ) :=
    (Homeomorph.Set.univ ℝ).contractibleSpace_iff.mpr inferInstance
  apply SimplyConnectedSpace.ofContractible

/-- A continuous nowhere-zero `γ : ℝ → ℂ` has a continuous logarithm on all of `ℝ`. -/
theorem exists_contLog {γ : ℝ → ℂ} (hγ : Continuous γ) (h0 : ∀ t, γ t ≠ 0) :
    ∃ L : ℝ → ℂ, Continuous L ∧ ∀ t, exp (L t) = γ t := by
  obtain ⟨f, hfc, hf⟩ := Complex.exists_continuousOn_eqOn_exp_comp realUniv_isSimplyConnected
    isOpen_univ hγ.continuousOn (by rintro ⟨z, -, hz⟩; exact h0 z hz)
  exact ⟨f, continuousOn_univ.mp hfc, fun t => by simpa [Function.comp] using hf (mem_univ t)⟩

/-- **Branch-independence of the log increment.**  Any two continuous logarithms of the same function
have the same increment `L b − L a`: their difference is a continuous `2πiℤ`-valued function on the
connected line, hence constant. -/
theorem contLog_increment_indep {L L' : ℝ → ℂ} (hLc : Continuous L) (hL'c : Continuous L')
    (hgd : ∀ t, exp (L t) = exp (L' t)) (a b : ℝ) :
    L b - L a = L' b - L' a := by
  set d : ℝ → ℂ := fun t => L t - L' t with hd
  have hdc : Continuous d := hLc.sub hL'c
  have hmem : ∀ t, ∃ k : ℤ, d t = (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    intro t
    have h1 : exp (d t) = 1 := by
      rw [hd]; simp only; rw [Complex.exp_sub, hgd t]; exact div_self (Complex.exp_ne_zero _)
    exact (Complex.exp_eq_one_iff).mp h1
  choose n hn using hmem
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hncont : Continuous n := by
    rw [Complex.isClosedEmbedding_intCast.isEmbedding.continuous_iff]
    have hcomp : (Int.cast ∘ n : ℝ → ℂ) = fun t => d t / (2 * (Real.pi : ℂ) * I) := by
      funext t; simp only [Function.comp_apply]; rw [hn t]; field_simp
    rw [hcomp]; exact hdc.div_const _
  have hlc : IsLocallyConstant n := (IsLocallyConstant.iff_continuous n).mpr hncont
  have hnab : n a = n b :=
    hlc.apply_eq_of_isPreconnected isPreconnected_univ (mem_univ a) (mem_univ b)
  have hdab : d a = d b := by rw [hn a, hn b, hnab]
  rw [hd] at hdab; simp only at hdab
  linear_combination -hdab

/-! ### §2 The loop, its winding number, and the increment law -/

/-- A nonvanishing loop on `[a,b]`: continuous and nowhere zero on `ℝ`, with matching endpoints. -/
structure IsLoop (γ : ℝ → ℂ) (a b : ℝ) : Prop where
  continuous : Continuous γ
  nonzero : ∀ t, γ t ≠ 0
  closed : γ a = γ b

/-- A canonical continuous logarithm of `γ` (arbitrary off the nonvanishing case). -/
noncomputable def contLog (γ : ℝ → ℂ) : ℝ → ℂ :=
  if h : Continuous γ ∧ ∀ t, γ t ≠ 0 then (exists_contLog h.1 h.2).choose else 0

theorem contLog_spec {γ : ℝ → ℂ} (hc : Continuous γ) (h0 : ∀ t, γ t ≠ 0) :
    Continuous (contLog γ) ∧ ∀ t, exp (contLog γ t) = γ t := by
  rw [contLog, dif_pos ⟨hc, h0⟩]; exact (exists_contLog hc h0).choose_spec

/-- The integer increment of a function whose value increment lies in `2πiℤ` (else `0`). -/
noncomputable def windIncr (L : ℝ → ℂ) (a b : ℝ) : ℤ :=
  if h : ∃ k : ℤ, L b - L a = (k : ℂ) * (2 * (Real.pi : ℂ) * I) then h.choose else 0

theorem windIncr_spec {L : ℝ → ℂ} {a b : ℝ}
    (h : ∃ k : ℤ, L b - L a = (k : ℂ) * (2 * (Real.pi : ℂ) * I)) :
    L b - L a = (windIncr L a b : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  rw [windIncr, dif_pos h]; exact h.choose_spec

/-- **The winding number** of a nonvanishing loop: the integer `k` with `L b − L a = 2πi·k` for the
canonical logarithm `L` of `γ`. -/
noncomputable def windingNumber (γ : ℝ → ℂ) (a b : ℝ) : ℤ := windIncr (contLog γ) a b

/-- **The increment law.**  For *any* continuous logarithm `L` of a nonvanishing loop `γ`,
`L b − L a = 2πi · windingNumber γ a b`.  (Branch-independence makes this hold for every `L`, not
only the canonical one.) -/
theorem contLog_increment {γ : ℝ → ℂ} {a b : ℝ} (hL : IsLoop γ a b)
    {L : ℝ → ℂ} (hLc : Continuous L) (hLe : ∀ t, exp (L t) = γ t) :
    L b - L a = (windingNumber γ a b : ℂ) * (2 * (Real.pi : ℂ) * I) := by
  obtain ⟨hcL, hce⟩ := contLog_spec hL.continuous hL.nonzero
  have hind : L b - L a = contLog γ b - contLog γ a :=
    contLog_increment_indep hLc hcL (fun t => by rw [hLe t, hce t]) a b
  have hex : ∃ k : ℤ, contLog γ b - contLog γ a = (k : ℂ) * (2 * (Real.pi : ℂ) * I) := by
    rw [← Complex.exp_eq_one_iff, Complex.exp_sub, hce b, hce a, hL.closed]
    exact div_self (hL.nonzero b)
  rw [hind]; exact windIncr_spec hex

/-! ### §3 The calculus: vanishing, constants, additivity, powers -/

/-- **Vanishing ⟺ the logarithm closes up.**  The winding number is zero exactly when a (any)
continuous logarithm of the loop returns to its start — equivalently the loop lifts to a *closed*
path, equivalently it bounds a continuous root of every order. -/
theorem windingNumber_eq_zero_iff {γ : ℝ → ℂ} {a b : ℝ} (hL : IsLoop γ a b)
    {L : ℝ → ℂ} (hLc : Continuous L) (hLe : ∀ t, exp (L t) = γ t) :
    windingNumber γ a b = 0 ↔ L b = L a := by
  have hincr := contLog_increment hL hLc hLe
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Complex.I_ne_zero, Real.pi_ne_zero]
  constructor
  · intro h; rw [h] at hincr; simp only [Int.cast_zero, zero_mul] at hincr
    exact sub_eq_zero.mp hincr
  · intro h; rw [h, sub_self] at hincr
    have : (windingNumber γ a b : ℂ) = 0 := by
      rcases mul_eq_zero.mp hincr.symm with h' | h'
      · exact h'
      · exact absurd h' h2pi
    exact_mod_cast this

/-- **A constant loop has winding number zero.** -/
theorem windingNumber_const {c : ℂ} (hc : c ≠ 0) (a b : ℝ) :
    windingNumber (fun _ => c) a b = 0 :=
  (windingNumber_eq_zero_iff ⟨continuous_const, fun _ => hc, rfl⟩ continuous_const
    (fun _ => Complex.exp_log hc)).mpr rfl

/-- **Additivity.**  The winding number of a product of loops is the sum of the winding numbers —
the loop form of `wCharge_add` before reduction. -/
theorem windingNumber_mul {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ}
    (h₁ : IsLoop γ₁ a b) (h₂ : IsLoop γ₂ a b) :
    windingNumber (fun t => γ₁ t * γ₂ t) a b = windingNumber γ₁ a b + windingNumber γ₂ a b := by
  have hp : IsLoop (fun t => γ₁ t * γ₂ t) a b :=
    ⟨h₁.continuous.mul h₂.continuous, fun t => mul_ne_zero (h₁.nonzero t) (h₂.nonzero t),
      by simp only [h₁.closed, h₂.closed]⟩
  obtain ⟨hc1, he1⟩ := contLog_spec h₁.continuous h₁.nonzero
  obtain ⟨hc2, he2⟩ := contLog_spec h₂.continuous h₂.nonzero
  have hsumlog : ∀ t, exp (contLog γ₁ t + contLog γ₂ t) = γ₁ t * γ₂ t := by
    intro t; rw [Complex.exp_add, he1 t, he2 t]
  have key := contLog_increment hp (L := fun t => contLog γ₁ t + contLog γ₂ t) (hc1.add hc2) hsumlog
  have k1 := contLog_increment h₁ hc1 he1
  have k2 := contLog_increment h₂ hc2 he2
  have h2pi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hcombine : (windingNumber (fun t => γ₁ t * γ₂ t) a b : ℂ) * (2 * (Real.pi : ℂ) * I)
      = ((windingNumber γ₁ a b : ℂ) + (windingNumber γ₂ a b : ℂ)) * (2 * (Real.pi : ℂ) * I) := by
    rw [← key]
    have hexp : (contLog γ₁ b + contLog γ₂ b) - (contLog γ₁ a + contLog γ₂ a)
        = (contLog γ₁ b - contLog γ₁ a) + (contLog γ₂ b - contLog γ₂ a) := by ring
    rw [hexp, k1, k2]; ring
  have hcast : (windingNumber (fun t => γ₁ t * γ₂ t) a b : ℂ)
      = (windingNumber γ₁ a b : ℂ) + (windingNumber γ₂ a b : ℂ) :=
    mul_right_cancel₀ h2pi hcombine
  exact_mod_cast hcast

/-- **Power law.**  The winding number of the `r`-th power of a loop is `r` times the winding number
— the loop form of the charge power law. -/
theorem windingNumber_pow {γ : ℝ → ℂ} {a b : ℝ} (hL : IsLoop γ a b) (r : ℕ) :
    windingNumber (fun t => (γ t) ^ r) a b = r * windingNumber γ a b := by
  induction r with
  | zero => simpa using windingNumber_const (one_ne_zero) a b
  | succ m ih =>
    have hpow : IsLoop (fun t => (γ t) ^ m) a b :=
      ⟨hL.continuous.pow m, fun t => pow_ne_zero m (hL.nonzero t), by simp only [hL.closed]⟩
    have hmul := windingNumber_mul hpow hL
    have hgoal : (fun t => (γ t) ^ (m + 1)) = (fun t => (γ t) ^ m * γ t) := by
      funext t; rw [pow_succ]
    rw [hgoal, hmul, ih]; push_cast; ring

/-! ### §4 The loop deck charge: the winding number mod `2^k` -/

/-- The rung-`k` deck charge of a loop: its winding number reduced mod `2^k` — the loop realisation
of the abstract `wCharge`, i.e. the obstruction to a continuous `2^k`-th root along `γ`. -/
noncomputable def loopCharge (k : ℕ) (γ : ℝ → ℂ) (a b : ℝ) : ZMod (2 ^ k) :=
  wCharge (2 ^ k) (windingNumber γ a b)

/-- The loop charge is additive over products (its winding number is). -/
theorem loopCharge_mul {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} (k : ℕ)
    (h₁ : IsLoop γ₁ a b) (h₂ : IsLoop γ₂ a b) :
    loopCharge k (fun t => γ₁ t * γ₂ t) a b = loopCharge k γ₁ a b + loopCharge k γ₂ a b := by
  rw [loopCharge, loopCharge, loopCharge, windingNumber_mul h₁ h₂, wCharge_add]

/-- The loop charge scales under powers. -/
theorem loopCharge_pow {γ : ℝ → ℂ} {a b : ℝ} (k : ℕ) (hL : IsLoop γ a b) (r : ℕ) :
    loopCharge k (fun t => (γ t) ^ r) a b = r • loopCharge k γ a b := by
  rw [loopCharge, loopCharge, windingNumber_pow hL r, wCharge_nsmul]

/-- **Vanishing of the loop charge ⟺ the winding number is divisible by `2^k`** — the loop form of
`wCharge_eq_zero_iff`.  Trivial charge is exactly the obstruction-free case where a continuous
`2^k`-th root exists along `γ`. -/
theorem loopCharge_eq_zero_iff (k : ℕ) (γ : ℝ → ℂ) (a b : ℝ) :
    loopCharge k γ a b = 0 ↔ (2 ^ k : ℤ) ∣ windingNumber γ a b := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [loopCharge, wCharge_eq_zero_iff]
  norm_cast

end RHTower
